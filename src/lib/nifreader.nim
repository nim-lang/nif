#       Nif library
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## High performance ("zero copies") NIF file reader.

import std / [memfiles, tables, parseutils]
import stringviews

const
  ControlChars = {'(', ')', '[', ']', '{', '}', '@', '#', '\'', '"', ':'}
  ControlCharsOrWhite = ControlChars + {' ', '\n', '\t', '\r'}
  HexChars* = {'0'..'9', 'A'..'F'} # lowercase letters are not in the NIF spec!
  StringSuffixChars = {'A'..'Z', 'a'..'z', '_', '0'..'9'}
  NumberSuffixChars = {'a'..'z', '_', '0'..'9'}
  Digits = {'0'..'9'}

type
  TokenKind* = enum
    UnknownToken, EofToken, ParLe, ParRi,
    DotToken, Ident, Symbol, SymbolDef,
    StringLit, CharLit, IntLit, UIntLit, FloatLit

  FilePos* = object
    col*, line*: int32

  TokenFlag = enum
    TokenHasEscapes, FilenameHasEscapes

  Token* = object
    tk*: TokenKind
    flags: set[TokenFlag]
    kind*: uint16   # for clients to fill in ("known node kinds")
    s*: StringView
    pos*: FilePos
    suffix*: StringView
    filename*: StringView

  MetaInfo* = object
    dialect*: StringView
    vendor*: StringView
    platform*: StringView
    config*: StringView

  Reader* = object
    p: pchar
    eof: pchar
    lineStart: pchar
    f: MemFile
    err: bool
    isubs, ksubs: Table[StringView, (TokenKind, StringView)]
    nifPos: FilePos # file position within the NIF file, not affected by '@' annotations
    meta: MetaInfo

proc `$`*(t: Token): string =
  case t.tk
  of UnknownToken: result = "<unknown token>"
  of EofToken: result = "<eof>"
  of ParLe: result = "(" & $t.s
  of ParRi: result = ")"
  of DotToken: result = "."
  of Ident, Symbol, SymbolDef,
     StringLit, CharLit, IntLit, UIntLit, FloatLit:
    result = $t.tk & ":" & $t.s

template inc(p: pchar; diff = 1) =
  p = cast[pchar](cast[int](p) + diff)

template `+!`(p: pchar; diff: int): pchar =
  cast[pchar](cast[int](p) + diff)

template `-!`(a, b: pchar): int = cast[int](a) - cast[int](b)

template `^`(p: pchar): char = p[0]

proc open*(filename: string): Reader =
  var err = false
  let f = try:
            memfiles.open(filename)
          except:
            err = true
            default(MemFile)
  result = Reader(f: f, err: err, p: nil)
  if not err:
    result.p = cast[pchar](result.f.mem)
    result.eof = result.p
    inc result.eof, result.f.size

proc close*(r: var Reader) =
  if not r.err: close r.f

proc skipWhitespace(r: var Reader) =
  while r.p < r.eof:
    case ^r.p
    of ' ', '\t':
      inc r.p
    of '\n':
      inc r.p
      r.lineStart = r.p
      inc r.nifPos.line
    else:
      break

proc skipComment(r: var Reader) {.inline.} =
  while r.p < r.eof:
    if ^r.p == '#':
      inc r.p
      break
    elif ^r.p == '\n':
      inc r.p
      r.lineStart = r.p
      inc r.nifPos.line
    else:
      inc r.p

proc handleHex(p: pchar): char =
  var output = 0
  case p[0]
  of '0'..'9':
    output = output shl 4 or (ord(p[0]) - ord('0'))
  of 'A'..'F':
    output = output shl 4 or (ord(p[0]) - ord('A') + 10)
  else: discard
  case p[1]
  of '0'..'9':
    output = output shl 4 or (ord(p[1]) - ord('0'))
  of 'A'..'F':
    output = output shl 4 or (ord(p[1]) - ord('A') + 10)
  else: discard
  result = char(output)

proc decodeChar*(t: Token): char =
  assert t.tk == CharLit
  result = ^t.s.p
  if result == '\\':
    var p = t.s.p
    inc p
    result = handleHex(p)

proc decodeStr*(t: Token): string =
  if TokenHasEscapes in t.flags:
    result = ""
    var p = t.s.p
    let sentinel = p +! t.s.len
    while p < sentinel:
      if ^p == '\\':
        result.add handleHex(p)
        inc p, 2
      else:
        result.add ^p
      inc p
  else:
    result = newString(t.s.len)
    copyMem(addr result[0], t.s.p, t.s.len)

proc decodeFilename*(t: Token): string =
  if FilenameHasEscapes in t.flags:
    result = ""
    var p = t.filename.p
    let sentinel = p +! t.filename.len
    while p < sentinel:
      if ^p == '\\':
        result.add handleHex(p)
        inc p, 2
      else:
        result.add ^p
      inc p
  else:
    result = newString(t.filename.len)
    copyMem(addr result[0], t.filename.p, t.filename.len)

proc decodeFloat*(t: Token): BiggestFloat =
  assert t.tk == FloatLit
  let res = parseutils.parseBiggestFloat(toOpenArray(t.s.p, 0, t.s.len-1), result)
  assert res == t.s.len

proc decodeUInt*(t: Token): BiggestUInt =
  assert t.tk == UIntLit
  let res = parseutils.parseBiggestUInt(toOpenArray(t.s.p, 0, t.s.len-1), result)
  assert res == t.s.len

proc decodeInt*(t: Token): BiggestInt =
  assert t.tk == IntLit
  let res = parseutils.parseBiggestInt(toOpenArray(t.s.p, 0, t.s.len-1), result)
  assert res == t.s.len

proc handleNumber(r: var Reader; result: var Token) =
  if r.p < r.eof and ^r.p in Digits:
    result.tk = IntLit # overwritten if we detect a float or unsigned
    while r.p < r.eof and ^r.p in Digits:
      inc r.p
      inc result.s.len

    if r.p < r.eof and ^r.p == '.':
      result.tk = FloatLit
      inc r.p
      inc result.s.len
      while r.p < r.eof and ^r.p in Digits:
        inc r.p
        inc result.s.len

    if r.p < r.eof and ^r.p == 'E':
      result.tk = FloatLit
      inc r.p
      inc result.s.len
      if r.p < r.eof and ^r.p == '-':
        inc r.p
        inc result.s.len
      while r.p < r.eof and ^r.p in Digits:
        inc r.p
        inc result.s.len
    if r.p < r.eof and ^r.p in NumberSuffixChars:
      result.suffix.p = r.p
      if ^r.p == 'u': result.tk = UIntLit
      elif ^r.p == 'f': result.tk = FloatLit
      while r.p < r.eof and ^r.p in NumberSuffixChars:
        inc r.p
        inc result.suffix.len

proc handleLineInfo(r: var Reader; result: var Token) =
  var col = 0
  while r.p < r.eof and ^r.p in Digits:
    let c = ord(^r.p) - ord('0')
    if col >= (low(int) + c) div 10:
      col = col * 10 + c
    inc r.p

  var line = 0
  if r.p < r.eof and ^r.p == ',':
    inc r.p
    while r.p < r.eof and ^r.p in Digits:
      let c = ord(^r.p) - ord('0')
      if line >= (low(int) + c) div 10:
        line = line * 10 + c
      inc r.p

  result.pos = FilePos(col: col.int32, line: line.int32)

  if r.p < r.eof and ^r.p == ',':
    inc r.p
    result.filename.p = r.p
    while r.p < r.eof:
      let ch = ^r.p
      if ch in ControlCharsOrWhite:
        break
      elif ch == '\\':
        result.flags.incl FilenameHasEscapes
      elif ch == '\n':
        r.lineStart = r.p
        inc r.nifPos.line
      inc result.filename.len
      inc r.p

proc next*(r: var Reader): Token =
  # Returning a new Token is somewhat unusual but lets clients
  # create implicit trees on the stack.
  result = default(Token)
  if r.p >= r.eof:
    result.tk = EofToken
  else:
    skipWhitespace r
    if ^r.p == '@':
      # we have node prefix
      inc r.p
      handleLineInfo r, result
      skipWhitespace r

    if ^r.p == '#':
      # we have a node comment, just skip it:
      skipComment r
      skipWhitespace r

    case ^r.p
    of '(':
      result.tk = ParLe
      inc r.p
      result.s.p = r.p
      result.s.len = 0
      while r.p < r.eof and ^r.p notin ControlCharsOrWhite:
        inc result.s.len
        inc r.p
      let repl = r.ksubs.getOrDefault(result.s)
      if repl[0] != UnknownToken:
        result.s = repl[1]
    of ')':
      result.tk = ParRi
      inc r.p
    of '.':
      result.tk = DotToken
      inc r.p
    of '"':
      inc r.p
      result.tk = StringLit
      result.s.p = r.p
      result.s.len = 0
      while r.p < r.eof:
        let ch = ^r.p
        if ch == '"':
          inc r.p
          break
        elif ch == '\\':
          result.flags.incl TokenHasEscapes
        elif ch == '\n':
          r.lineStart = r.p
          inc r.nifPos.line
        inc result.s.len
        inc r.p

      if r.p < r.eof and ^r.p in StringSuffixChars:
        result.suffix.p = r.p
        while true:
          inc r.p
          inc result.suffix.len
          if r.p == r.eof or ^r.p notin StringSuffixChars: break
    of '\'':
      inc r.p
      result.s.p = r.p
      if ^r.p == '\\':
        result.flags.incl TokenHasEscapes
        inc r.p
        if r.p[0] in HexChars and r.p[1] in HexChars:
          inc r.p, 2
          if ^r.p == '\'':
            inc r.p
            result.tk = CharLit # now valid
      elif ^r.p in ControlChars:
        discard "keep it as UnknownToken"
      else:
        inc r.p
        if ^r.p == '\'':
          inc r.p
          result.tk = CharLit # only now valid

    of ':':
      inc r.p
      result.s.p = r.p
      while r.p < r.eof and ^r.p notin ControlCharsOrWhite:
        if ^r.p == '\\': result.flags.incl TokenHasEscapes
        inc result.s.len
        inc r.p
      if result.s.len > 0:
        result.tk = SymbolDef
        let repl = r.isubs.getOrDefault(result.s)
        if repl[0] == Symbol:
          result.s = repl[1]
        else:
          result.tk = UnknownToken # error

    of '-':
      result.s.p = r.p
      inc r.p
      inc result.s.len
      handleNumber r, result

    of '0'..'9':
      result.s.p = r.p
      handleNumber r, result

    else:
      result.s.p = r.p
      var hasDot = false
      while r.p < r.eof and ^r.p notin ControlCharsOrWhite:
        if ^r.p == '\\': result.flags.incl TokenHasEscapes
        elif ^r.p == '.': hasDot = true
        inc result.s.len
        inc r.p

      if result.s.len > 0:
        result.tk = if hasDot: Symbol else: Ident
        let repl = r.isubs.getOrDefault(result.s)
        if repl[0] != UnknownToken:
          result.tk = repl[0]
          result.s = repl[1]

    r.nifPos.col = int32(r.p -! r.lineStart)

const
  Cookie = "(.nif24)"

type
  DirectivesResult* = enum
    WrongHeader, WrongMeta, Success

proc startsWith*(r: Reader; prefix: string): bool =
  let prefixLen = prefix.len
  var i = 0
  var p = r.p
  while true:
    if i >= prefixLen: return true
    if p >= r.eof or ^p != prefix[i]: return false
    inc p
    inc i

proc processDirectives*(r: var Reader): DirectivesResult =
  template handleSubstitutionPair(r: var Reader; valid: set[TokenKind]; subs: typed) =
    if r.p < r.eof and ^r.p in ControlCharsOrWhite:
      let key = next(r)
      if key.tk == Ident:
        let val = next(r)
        let closingPar = next(r)
        if closingPar.tk == ParRi and val.tk in valid:
          subs[key.s] = (val.tk, val.s)

  template handleMeta(r: var Reader; field: untyped) =
    let value = next(r)
    if value.tk == StringLit:
      field = value.s
    else:
      result = WrongMeta
    while true:
      var closePar = next(r)
      if closePar.tk in {ParRi, EofToken}: break

  if r.startsWith(Cookie):
    result = Success
    inc r.p, Cookie.len
    while true:
      skipWhitespace r
      if r.startsWith("(.k"):
        inc r.p, len("(.k")
        # extension: let node kinds have dots! `(atomic.inc ...)`
        handleSubstitutionPair r, {Ident, Symbol}, r.ksubs
      elif r.startsWith("(.i"):
        inc r.p, len("(.i")
        handleSubstitutionPair r, {Ident, Symbol, StringLit, CharLit, IntLit, UIntLit, FloatLit}, r.isubs
      elif r.startsWith("(."):
        let directive = next(r)
        assert directive.tk == ParLe
        if directive.s == ".vendor":
          handleMeta r, r.meta.vendor
        elif directive.s == ".platform":
          handleMeta r, r.meta.platform
        elif directive.s == ".dialect":
          handleMeta r, r.meta.dialect
        elif directive.s == ".config":
          handleMeta r, r.meta.config
        else:
          # skip unknown directive
          while true:
            var closePar = next(r)
            if closePar.tk in {ParRi, EofToken}: break
      else:
        break
  else:
    result = WrongHeader
