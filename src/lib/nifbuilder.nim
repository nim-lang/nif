#       Nif library
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Support code for generating NIF code.

type
  Mode = enum
    UsesMem, UsesFile
  Builder* = object ## A builder can be in-memory or directly write into a file.
                    ## In the end either `extract` or `close` must be called.
    buf: string
    mode: Mode
    compact: bool
    f: File
    nesting: int

proc `=copy`(dest: var Builder; src: Builder) {.error.}

proc open*(filename: string; compact = false): Builder =
  ## Opens a new builder and attached it to some output filename.
  Builder(f: open(filename, fmWrite), mode: UsesFile, compact: compact)

proc open*(sizeHint: int; compact = false): Builder =
  ## Opens a new builder with the intent to keep the produced
  ## code in memory.
  Builder(buf: newStringOfCap(sizeHint), mode: UsesMem, compact: compact)

proc attachedToFile*(b: Builder): bool {.inline.} = b.mode == UsesFile

proc extract*(b: sink Builder): string =
  ## Extracts the buffer from the builder.
  ## The builder should not be used afterwards.
  assert b.nesting == 0, "unpaired '(' or ')'"
  assert b.mode == UsesMem, "cannot extract from a file"
  result = move(b.buf)

proc close*(b: var Builder) =
  if b.mode == UsesFile:
    write b.f, b.buf
    close b.f
  assert b.nesting == 0, "unpaired '(' or ')'"

proc putPending(b: var Builder; s: string) =
  b.buf.add s

proc drainPending(b: var Builder) =
  if b.mode == UsesFile:
    # handle pending data:
    write b.f, b.buf
    b.buf.setLen 0

proc put(b: var Builder; s: string) =
  if b.mode == UsesFile:
    drainPending b
    write b.f, s
  else:
    b.buf.add s

proc put(b: var Builder; s: char) =
  if b.mode == UsesFile:
    drainPending b
    write b.f, s
  else:
    b.buf.add s

proc undoWhitespace(b: var Builder) =
  var i = b.buf.len - 1
  while i >= 0 and b.buf[i] in {' ', '\n'}: dec i
  b.buf.setLen i+1


const
  ControlChars* = {'(', ')', '[', ']', '{', '}', '@', '#', '\'', '"', '\\', ':'}

proc escape(b: var Builder; c: char) =
  const HexChars = "0123456789ABCDEF"
  var n = int(c)
  b.put '\\'
  b.put HexChars[n shr 4 and 0xF]
  b.put HexChars[n and 0xF]

template needsEscape(c: char): bool = c < ' ' or c in ControlChars

proc addRaw*(b: var Builder; s: string) =
  put b, s

proc addSep(b: var Builder) =
  if b.buf.len > 0 and b.buf[b.buf.len-1] == '\n':
    discard "space not required"
  elif b.nesting != 0:
    b.putPending " "

#  ------------ Atoms ------------------------

proc addIdent*(b: var Builder; s: string) =
  addSep b
  for c in s:
    if c < ' ' or (c in ControlChars+{'.'}):
      b.escape c
    else:
      b.put c

proc addSymbol*(b: var Builder; s: string) =
  addSep b
  for c in s:
    if c.needsEscape:
      b.escape c
    else:
      b.put c

proc addSymbolDef*(b: var Builder; s: string) =
  addSep b
  b.put ':'
  for c in s:
    if c.needsEscape:
      b.escape c
    else:
      b.put c

proc addStrLit*(b: var Builder; s: string; suffix = "") =
  addSep b
  b.put '"'
  for c in s:
    if c in ControlChars:
      b.escape c
    else:
      b.put c
  b.put '"'
  b.put suffix

proc addEmpty*(b: var Builder; count = 1) =
  addSep b
  for i in 1..count:
    b.put '.'

proc addCharLit*(b: var Builder; c: char) =
  addSep b
  b.put '\''
  if c.needsEscape:
    escape b, c
  else:
    b.put c
  b.put '\''

proc addIntLit*(b: var Builder; i: BiggestInt; suffix = "") =
  addSep b
  b.put $i
  b.put suffix

proc addUIntLit*(b: var Builder; u: BiggestUInt; suffix = "") =
  addSep b
  b.put $u
  b.put suffix

proc addFloatLit*(b: var Builder; f: BiggestFloat; suffix = "") =
  addSep b
  let myLen = b.buf.len
  drainPending b
  b.buf.addFloat f
  for i in myLen ..< b.buf.len:
    if b.buf[i] == 'e': b.buf[i] = 'E'
  if b.mode == UsesFile:
    b.f.write b.buf
    b.buf.setLen 0
  b.put suffix

proc addLineInfo*(b: var Builder; col, line: int32; file = "") =
  addSep b
  var seps = 0
  if col != 0'i32:
    drainPending b
    b.buf.add '@'
    b.buf.addInt col
    inc seps
  if line != 0'i32:
    if seps == 0:
      drainPending b
      b.buf.add '@'
    b.buf.add ','
    b.buf.addInt line
    inc seps
  if file.len > 0:
    if seps == 0:
      drainPending b
      b.buf.add "@,,"
    elif seps == 1: b.buf.add "@,"
    else: b.buf.add ','
    for c in file:
      if c.needsEscape:
        b.escape c
      else:
        b.put c

proc addKeyw*(b: var Builder; keyw: string) =
  ## Adds a complete compound node that has no children like `(nil)`.
  drainPending b
  b.put '('
  b.put keyw
  b.put ')'

proc addTree*(b: var Builder; kind: string) =
  ## Starts a new compound node. Must be closed with `endTree`.
  ## See also `withTree`.
  ## `kind` is allowed to start with a dot. This emits a directive then.
  drainPending b
  if not b.compact:
    b.put "\n"
    for i in 1..b.nesting: b.put ' '
    b.put '('
  else:
    b.put "\n("
  b.put kind
  inc b.nesting

proc endTree*(b: var Builder) =
  assert b.nesting > 0, "generating ')' would produce a syntax error"
  dec b.nesting
  undoWhitespace b
  b.put ')'

template withTree*(b: var Builder; kind: string; body: untyped) =
  ## Convenience template that wraps `body` around `addTree` and `endTree`
  ## calls.
  addTree b, kind
  body
  endTree b

proc addHeader*(b: var Builder; vendor = "", dialect = "") =
  b.put "(.nif24)\n"
  if vendor.len > 0:
    b.put "(.vendor "
    b.addStrLit vendor
    b.put ")\n"
  if dialect.len > 0:
    b.put "(.dialect "
    b.addStrLit dialect
    b.put ")\n"

proc addFlags*[T: enum](b: var Builder; kind: string; flags: set[T]) =
  ## Little helper for converting a set of enum to NIF. If `flags` is
  ## the empty set, nothing is emitted.
  if flags == {}:
    discard "omit empty flags in order to save space"
  else:
    withTree b, kind:
      for x in items(flags):
        b.addIdent $x

when isMainModule:
  proc test(b: sink Builder) =
    b.addHeader "tester", "niftest"
    b.withTree "stmts":
      b.addLineInfo 4, 5, "mymodb.nim"
      b.withTree "call":
        b.addLineInfo 1, 3, "mymod.nim"
        b.addSymbol "foo.3.mymod"
        b.addIntLit 3423
        b.addFloatLit 50.4

    if b.attachedToFile:
      b.close
    else:
      echo b.extract()

  proc main() =
    var b = open(10)
    test b

    var b2 = open"builder_example.nif"
    test b2

  main()
