#       Nifler
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Module that helps to emit NIF code, somewhat nicely formatted.

type
  Emitter* = object # state we need in order to do some formatting
    #minified*: bool # produce minified code
    output*: string
    nesting, lineLen: int

const
  ControlChars* = {'(', ')', '[', ']', '{', '}', '@', '#', '\'', '"', '\\', ':'}

proc lineBreak*(r: var string; l: var int; nesting: int) =
  r.add "\n"
  for i in 1 .. nesting*2: r.add ' '
  l = nesting*2

proc emit(em: var Emitter; token: string; l: int) =
  em.output.add token
  inc em.lineLen, l

proc escape(r: var string; c: char) =
  const HexChars = "0123456789ABCDEF"
  var n = int(c)
  r.add '\\'
  r.add HexChars[n shr 4 and 0xF]
  r.add HexChars[n and 0xF]

template needsEscape(c: char): bool = c < ' ' or c in ControlChars

proc addRaw*(em: var Emitter; r: string) =
  emit em, r, r.len

proc addIdent*(em: var Emitter; s: string) =
  var r = ""
  for c in s:
    if c.needsEscape:
      r.escape c
    else:
      r.add c
  emit em, r, r.len

proc addStrLit*(em: var Emitter; s, suffix: string) =
  var r = "\""
  var l = em.lineLen + 1
  var lastPart = 1
  for c in s:
    if l > 80:
      var endedInSpace = false
      if r.len > 0 and r[r.len-1] == ' ':
        endedInSpace = true
        setLen r, r.len - 1
      lineBreak(r, l, em.nesting)
      lastPart = em.nesting * 2
      if endedInSpace:
        r.add "\\20"
        inc l, 3
        inc lastPart, 3
    if c.needsEscape:
      r.escape c
      inc l, 3
      inc lastPart, 3
    else:
      r.add c
      inc l, 1
      inc lastPart, 1
  r.add "\""
  em.emit r, lastPart
  em.emit suffix, suffix.len


type
  NodeEmitter* = object
    i, innerLineLen, oldLen: int
    longMode: bool
    inner: string
    prefix: string

proc prepare*(em: var Emitter; kind: string): NodeEmitter =
  result = NodeEmitter(innerLineLen: em.lineLen, oldLen: em.output.len, prefix: kind)
  inc em.nesting
  swap em.output, result.inner

proc addSep*(em: var Emitter; n: var NodeEmitter) =
  if em.lineLen > 90:
    em.output.add "\n"
    for i in 0..<em.nesting*2: em.output.add ' '
    em.lineLen = em.nesting*2
    n.longMode = true
  else:
    em.output.add ' '
    inc em.lineLen

proc patch*(em: var Emitter; n: var NodeEmitter) =
  swap em.output, n.inner

  em.output.add '('
  em.output.add n.prefix
  var oldLen = n.oldLen
  if n.longMode or n.inner.len + n.prefix.len + em.lineLen > 89:
    em.output.add "\n"
    for i in 0..<em.nesting*2: em.output.add ' '
    em.output.add n.inner
    em.output.add "\n"
    em.lineLen = 0
    oldLen = em.output.len
    for i in 0..<(em.nesting-1)*2: em.output.add ' '
  else:
    em.output.add n.inner
  em.output.add ')'
  inc em.lineLen, em.output.len - oldLen
  dec em.nesting

proc addEmpty*(em: var Emitter; count = 1) =
  for i in 1..count:
    em.emit ".", 1

proc addCharLit*(em: var Emitter; c: char) =
  em.output.add '\''
  if c.needsEscape:
    escape em.output, c
    inc em.lineLen, 2
  else:
    em.output.add c
  em.output.add '\''
  inc em.lineLen, 3

template upateLen(body) =
  let oldLen = em.output.len
  body
  inc em.lineLen, em.output.len - oldLen

proc addIntLit*(em: var Emitter; i: BiggestInt; suffix = "") =
  upateLen:
    em.output.addInt i
    em.output.add suffix

proc addLine*(em: var Emitter; i: int32) =
  upateLen:
    em.output.addInt i

proc addUIntLit*(em: var Emitter; u: BiggestUInt; suffix = "") =
  upateLen:
    em.output.add $u
    em.output.add suffix

proc addFloatLit*(em: var Emitter; f: BiggestFloat; suffix = "") =
  let myLen = em.output.len
  upateLen:
    em.output.addFloat f
    for i in myLen ..< em.output.len:
      if em.output[i] == 'e': em.output[i] = 'E'
    em.output.add suffix

when isMainModule:
  var em = Emitter()
  var a = prepare(em, "proc")
  em.addSep a
  em.addStrLit "#(escaped?)\n"
  em.addSep a
  em.addStrLit "more here"
  em.patch(a)

  echo em.output
