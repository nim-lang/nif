#       Nif library
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## A NIF stream is simply a seq of tokens. It turns out to be useful
## for many different cases.

import std / [assertions, hashes]

import bitabs, stringviews, lineinfos, nifreader, nifbuilder

export TokenKind

const
  InlineInt* = EofToken

type
  PackedToken* = object     # 8 bytes
    x: uint32
    info*: PackedLineInfo

const
  TokenKindBits = 4'u32
  TokenKindMask = (1'u32 shl TokenKindBits) - 1'u32

template kind*(n: PackedToken): TokenKind = cast[TokenKind](n.x and TokenKindMask)
template uoperand*(n: PackedToken): uint32 = (n.x shr TokenKindBits)
template soperand*(n: PackedToken): int32 = cast[int32](uoperand(n))

template toX(k: TokenKind; operand: uint32): uint32 =
  uint32(k) or (operand shl TokenKindBits)

proc toToken*[L](kind: TokenKind; id: L; info: PackedLineInfo): PackedToken {.inline.} =
  PackedToken(x: toX(kind, uint32(id)), info: info)

proc addToken*[L](tree: var seq[PackedToken]; kind: TokenKind; id: L; info: PackedLineInfo) =
  tree.add PackedToken(x: toX(kind, uint32(id)), info: info)

type
  StrId* = distinct uint32
  SymId* = distinct uint32
  IntId* = distinct uint32
  UIntId* = distinct uint32
  FloatId* = distinct uint32
  TagId* = distinct uint32
  Literals* = object
    man*: LineInfoManager
    tags*: BiTable[TagId, string]
    files*: BiTable[FileId, string] # we cannot use StringView here as it may have unexpanded backslashes!
    syms*: BiTable[SymId, string]
    strings*: BiTable[StrId, string]
    integers*: BiTable[IntId, int64]
    uintegers*: BiTable[UIntId, uint64]
    floats*: BiTable[FloatId, float64]

proc `==`*(a, b: SymId): bool {.borrow.}
proc `==`*(a, b: StrId): bool {.borrow.}
proc `==`*(a, b: IntId): bool {.borrow.}
proc `==`*(a, b: UIntId): bool {.borrow.}
proc `==`*(a, b: FloatId): bool {.borrow.}
proc `==`*(a, b: TagId): bool {.borrow.}

proc hash*(x: SymId): Hash {.borrow.}
proc hash*(x: StrId): Hash {.borrow.}
proc hash*(x: IntId): Hash {.borrow.}
proc hash*(x: UIntId): Hash {.borrow.}
proc hash*(x: FloatId): Hash {.borrow.}
proc hash*(x: TagId): Hash {.borrow.}

const
  Suffixed* = TagId(1)

proc createLiterals*(): Literals =
  result = default(Literals)
  let t = result.tags.getOrIncl("suf")
  assert t == Suffixed

var pool* = createLiterals()

proc registerTag*(tag: string; expected: TagId) =
  ## Mostly useful for code generator like Nifgram.
  let t = pool.tags.getOrIncl(tag)
  assert t == expected, "tag " & tag & " expected Id " & $expected.uint32 &
      " but it is already of value " & $t.uint32

template copyInto*(dest: var seq[PackedToken]; tag: TagId; info: PackedLineInfo; body: untyped) =
  dest.addToken ParLe, tag, info
  body
  dest.addToken ParRi, 0'u32, info

template copyIntoUnchecked*(dest: var seq[PackedToken]; tag: string; info: PackedLineInfo; body: untyped) =
  dest.addToken ParLe, pool.strings.getOrIncl(tag), info
  body
  dest.addToken ParRi, 0'u32, info

template withSuffix(body) =
  if t.suffix.len > 0:
    copyInto(dest, Suffixed, currentInfo):
      body
      dest.addToken StringLit, pool.strings.getOrInclFromView(t.suffix), currentInfo
  else:
    body

type
  Stream* = object
    r: Reader
    parents: seq[PackedLineInfo]

proc open*(filename: string): Stream =
  result = Stream(r: nifreader.open(filename))
  result.parents.add NoLineInfo

proc openFromBuffer*(buf: sink string): Stream =
  result = Stream(r: nifreader.openFromBuffer(buf))
  result.parents.add NoLineInfo

proc close*(s: var Stream) = nifreader.close(s.r)

proc rawNext(s: var Stream; t: Token): PackedToken =
  var currentInfo = NoLineInfo
  if t.filename.len == 0:
    # relative file position
    if t.pos.line != 0 or t.pos.col != 0:
      let (file, line, col) = unpack(pool.man, s.parents[^1])
      currentInfo = pack(pool.man, file, line+t.pos.line, col+t.pos.col)
  else:
    # absolute file position:
    let fileId = pool.files.getOrIncl(decodeFilename t)
    currentInfo = pack(pool.man, fileId, t.pos.line, t.pos.col)

  case t.tk
  of ParRi, EofToken, UnknownToken, DotToken:
    result = toToken(ParRi, 0'u32, currentInfo)
  of ParLe:
    let ka = pool.tags.getOrInclFromView(t.s)
    result = toToken(ParLe, ka, currentInfo)
  of Ident, StringLit:
    result = toToken(t.tk, pool.strings.getOrIncl(decodeStr t), currentInfo)
  of Symbol, SymbolDef:
    result = toToken(t.tk, pool.syms.getOrIncl(decodeStr t), currentInfo)
  of CharLit:
    result = toToken(CharLit, uint32 decodeChar(t), currentInfo)
  of IntLit:
    result = toToken(IntLit, pool.integers.getOrIncl(decodeInt t), currentInfo)
  of UIntLit:
    result = toToken(UIntLit, pool.uintegers.getOrIncl(decodeUInt t), currentInfo)
  of FloatLit:
    result = toToken(FloatLit, pool.floats.getOrIncl(decodeFloat t), currentInfo)

proc next*(s: var Stream): PackedToken =
  let t = next(s.r)
  result = rawNext(s, t)

proc skip*(s: var Stream; current: PackedToken): PackedToken =
  if current.kind == ParLe:
    # jump to corresponding ParRi:
    var nested = 0
    while true:
      let t = next(s.r)
      if t.tk == ParLe: inc nested
      elif t.tk == ParRi:
        if nested == 0: break
        dec nested
  result = next(s)

proc parse*(r: var Reader; dest: var seq[PackedToken];
            parentInfo: PackedLineInfo): bool =
  let t = next(r)
  var currentInfo = parentInfo
  if t.filename.len == 0:
    # relative file position
    if t.pos.line != 0 or t.pos.col != 0:
      let (file, line, col) = unpack(pool.man, parentInfo)
      currentInfo = pack(pool.man, file, line+t.pos.line, col+t.pos.col)
  else:
    # absolute file position:
    let fileId = pool.files.getOrIncl(decodeFilename t)
    currentInfo = pack(pool.man, fileId, t.pos.line, t.pos.col)

  result = true
  case t.tk
  of ParRi:
    result = false
  of EofToken:
    result = false
  of ParLe:
    let ka = pool.tags.getOrInclFromView(t.s)
    copyInto(dest, ka, currentInfo):
      while true:
        let progress = parse(r, dest, currentInfo)
        if not progress: break

  of UnknownToken:
    copyIntoUnchecked dest, "errtok", currentInfo:
      dest.addToken StringLit, pool.strings.getOrIncl(decodeStr t), currentInfo
  of DotToken:
    dest.addToken DotToken, 0'u32, currentInfo
  of Ident:
    dest.addToken Ident, pool.strings.getOrIncl(decodeStr t), currentInfo
  of Symbol, SymbolDef:
    dest.addToken t.tk, pool.syms.getOrIncl(decodeStr t), currentInfo
  of CharLit:
    dest.addToken CharLit, uint32 decodeChar(t), currentInfo
  of StringLit:
    withSuffix:
      dest.addToken StringLit, pool.strings.getOrIncl(decodeStr t), currentInfo
  of IntLit:
    withSuffix:
      dest.addToken IntLit, pool.integers.getOrIncl(decodeInt t), currentInfo
  of UIntLit:
    withSuffix:
      dest.addToken UIntLit, pool.uintegers.getOrIncl(decodeUInt t), currentInfo
  of FloatLit:
    withSuffix:
      dest.addToken FloatLit, pool.floats.getOrIncl(decodeFloat t), currentInfo

proc litId*(n: PackedToken): StrId {.inline.} =
  assert n.kind in {Ident, StringLit}
  StrId(n.uoperand)

proc symId*(n: PackedToken): SymId {.inline.} =
  assert n.kind in {Symbol, SymbolDef}
  SymId(n.uoperand)

proc intId*(n: PackedToken): IntId {.inline.} =
  assert n.kind == IntLit
  IntId(n.uoperand)

proc uintId*(n: PackedToken): UIntId {.inline.} =
  assert n.kind == UIntLit
  UIntId(n.uoperand)

proc floatId*(n: PackedToken): FloatId {.inline.} =
  assert n.kind == FloatLit
  FloatId(n.uoperand)

proc tagId*(n: PackedToken): TagId {.inline.} =
  assert n.kind == ParLe, $n.kind
  TagId(n.uoperand)

proc `is`*(n: PackedToken; val: string): bool {.inline.} =
  n.kind == ParLe and pool.tags[n.tagId] == val

proc typebits*(n: PackedToken): int =
  if n.kind == IntLit:
    result = pool.integers[n.intId]
  elif n.kind == InlineInt:
    result = n.soperand
  else:
    result = 0

proc toString*(tree: openArray[PackedToken]): string =
  var b = nifbuilder.open(tree.len * 20)
  var stack: seq[PackedLineInfo] = @[]
  for n in 0 ..< tree.len:
    let info = tree[n].info
    if info.isValid:
      var (file, line, col) = unpack(pool.man, info)
      var fileAsStr = ""
      if stack.len > 0:
        let (pfile, pline, pcol) = unpack(pool.man, stack[^1])
        line = line - pline
        col = col - pcol
        if file != pfile: fileAsStr = pool.files[file]
      b.addLineInfo(col, line, fileAsStr)

    case tree[n].kind
    of DotToken:
      b.addEmpty()
    of Ident:
      b.addIdent(pool.strings[tree[n].litId])
    of Symbol:
      b.addSymbol(pool.syms[tree[n].symId])
    of IntLit:
      b.addIntLit(pool.integers[tree[n].intId])
    of UIntLit:
      b.addUIntLit(pool.uintegers[tree[n].uintId])
    of FloatLit:
      b.addFloatLit(pool.floats[tree[n].floatId])
    of SymbolDef:
      b.addSymbolDef(pool.syms[tree[n].symId])
    of CharLit:
      b.addCharLit char(tree[n].uoperand)
    of StringLit:
      b.addStrLit(pool.strings[tree[n].litId])
    of UnknownToken:
      b.addIdent "<unkonwn token>"
    of EofToken:
      b.addIntLit tree[n].soperand
    of ParRi:
      discard stack.pop()
      b.endTree()
    of ParLe:
      b.addTree(pool.tags[tree[n].tagId])
      stack.add info
  result = b.extract()
