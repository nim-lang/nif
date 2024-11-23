#       Nif library
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Cursors into token streams. Suprisingly effective even for more complex algorithms.

import std / assertions
import nifreader, nifstreams, bitabs, lineinfos

type
  Cursor* = object
    p: ptr PackedToken
    rem: int

const
  ErrToken = [toToken(ParLe, ErrT, NoLineInfo),
              toToken(ParRi, 0'u32, NoLineInfo)]

proc errCursor*(): Cursor =
  Cursor(p: addr ErrToken[0], rem: 2)

proc fromBuffer*(x: openArray[PackedToken]): Cursor {.inline.} =
  Cursor(p: addr(x[0]), rem: x.len)

proc setSpan*(c: var Cursor; beyondLast: Cursor) {.inline.} =
  c.rem = cast[int](beyondLast.p) - cast[int](c.p)

proc load*(c: Cursor): PackedToken {.inline.} = c.p[]

proc kind*(c: Cursor): TokenKind {.inline.} = c.load.kind

proc info*(c: Cursor): PackedLineInfo {.inline.} = c.load.info

proc litId*(c: Cursor): StrId {.inline.} = nifstreams.litId(c.load)
proc symId*(c: Cursor): SymId {.inline.} = nifstreams.symId(c.load)

proc intId*(c: Cursor): IntId {.inline.} = nifstreams.intId(c.load)
proc uintId*(c: Cursor): UIntId {.inline.} = nifstreams.uintId(c.load)
proc floatId*(c: Cursor): FloatId {.inline.} = nifstreams.floatId(c.load)
proc tagId*(c: Cursor): TagId {.inline.} = nifstreams.tagId(c.load)

proc tag*(c: Cursor): TagId {.inline.} = nifstreams.tag(c.load)

proc uoperand*(c: Cursor): uint32 {.inline.} = nifstreams.uoperand(c.load)
proc soperand*(c: Cursor): int32 {.inline.} = nifstreams.soperand(c.load)

proc inc*(c: var Cursor) {.inline.} =
  assert c.rem > 0
  c.p = cast[ptr PackedToken](cast[uint](c.p) + sizeof(PackedToken).uint)
  dec c.rem

proc unsafeDec*(c: var Cursor) {.inline.} =
  c.p = cast[ptr PackedToken](cast[uint](c.p) - sizeof(PackedToken).uint)
  inc c.rem

proc skip*(c: var Cursor) =
  if c.kind == ParLe:
    var nested = 0
    while true:
      inc c
      if c.kind == ParRi:
        if nested == 0: break
        dec nested
      elif c.kind == ParLe: inc nested
  inc c

type
  Storage = ptr UncheckedArray[PackedToken]
  TokenBuf* = object
    data: Storage
    len, cap, readers: int

proc `=copy`(dest: var TokenBuf; src: TokenBuf) {.error.}
when defined(nimAllowNonVarDestructor) and defined(gcDestructors):
  proc `=destroy`(dest: TokenBuf) {.inline.} =
    #assert dest.readers == 0, "TokenBuf still in use by some reader"
    if dest.data != nil: dealloc(dest.data)
else:
  proc `=destroy`(dest: var TokenBuf) {.inline.} =
    #assert dest.readers == 0, "TokenBuf still in use by some reader"
    if dest.data != nil: dealloc(dest.data)

proc createTokenBuf*(cap = 100): TokenBuf =
  result = TokenBuf(data: cast[Storage](alloc(sizeof(PackedToken)*cap)), len: 0, cap: cap)

proc isMutable(b: TokenBuf): bool {.inline.} = b.cap >= 0

proc freeze*(b: var TokenBuf) {.inline.} =
  if isMutable(b):
    b.cap = -(b.cap+1)

proc thaw*(b: var TokenBuf) =
  if not isMutable(b):
    b.cap = -(b.cap+1)

proc beginRead*(b: var TokenBuf): Cursor =
  if b.readers == 0: freeze(b)
  inc b.readers
  result = Cursor(p: addr(b.data[0]), rem: b.len)

proc endRead*(b: var TokenBuf; c: Cursor) =
  assert b.readers > 0, "unpaired endRead"
  dec b.readers
  if b.readers == 0: thaw(b)

proc add*(b: var TokenBuf; item: PackedToken) {.inline.} =
  assert isMutable(b), "attempt to mutate frozen TokenBuf"
  if b.len >= b.cap:
    b.cap = max(b.cap * 3 div 2, 8)
    b.data = cast[Storage](realloc(b.data, sizeof(PackedToken)*b.cap))
  b.data[b.len] = item
  inc b.len

proc len*(b: TokenBuf): int {.inline.} = b.len

proc `[]`*(b: TokenBuf; i: int): PackedToken {.inline.} =
  assert i >= 0 and i < b.len
  result = b.data[i]

proc `[]=`*(b: TokenBuf; i: int; val: PackedToken) {.inline.} =
  assert i >= 0 and i < b.len
  b.data[i] = val

proc cursorAt*(b: var TokenBuf; i: int): Cursor {.inline.} =
  assert i >= 0 and i < b.len
  if b.readers == 0: freeze(b)
  inc b.readers
  result = Cursor(p: addr b.data[i], rem: b.len-i)

proc add*(result: var TokenBuf; c: Cursor) =
  result.add c.load

proc addSubtree*(result: var TokenBuf; c: Cursor) =
  assert c.kind != ParRi, "cursor at end?"
  if c.kind != ParLe:
    # atom:
    result.add c.load
  else:
    var c = c
    var nested = 0
    while true:
      let item = c.load
      result.add item
      if item.kind == ParRi:
        dec nested
        if nested == 0: break
      elif item.kind == ParLe: inc nested
      inc c

proc addUnstructured*(result: var TokenBuf; c: Cursor) =
  var c = c
  while c.rem > 0:
    result.add c.load
    inc c

proc add*(result: var TokenBuf; s: var Stream) =
  let c = next(s)
  assert c.kind != ParRi, "cursor at end?"
  result.add c
  if c.kind == ParLe:
    var nested = 0
    while true:
      let item = next(s)
      result.add item
      if item.kind == ParRi:
        if nested == 0: break
        dec nested
      elif item.kind == ParLe: inc nested

iterator items*(b: TokenBuf): PackedToken =
  for i in 0 ..< b.len:
    yield b.data[i]

proc add*(dest: var TokenBuf; src: TokenBuf) =
  for t in items(src): dest.add t

proc fromCursor*(c: Cursor): TokenBuf =
  result = TokenBuf(data: cast[Storage](alloc(sizeof(PackedToken)*4)), len: 0, cap: 4)
  result.add c

proc fromStream*(s: var Stream): TokenBuf =
  result = TokenBuf(data: cast[Storage](alloc(sizeof(PackedToken)*4)), len: 0, cap: 4)
  result.add s

proc shrink*(b: var TokenBuf; newLen: int) =
  assert isMutable(b), "attempt to mutate frozen TokenBuf"
  assert newLen >= 0 and newLen <= b.len
  b.len = newLen

proc grow(b: var TokenBuf; newLen: int) =
  assert isMutable(b), "attempt to mutate frozen TokenBuf"
  assert newLen > b.len
  if b.cap < newLen:
    b.cap = max(b.cap * 3 div 2, newLen)
    b.data = cast[Storage](realloc(b.data, sizeof(PackedToken)*b.cap))
  b.len = newLen

template buildTree*(dest: var TokenBuf; tag: TagId; info: PackedLineInfo; body: untyped) =
  dest.add toToken(ParLe, tag, info)
  body
  dest.add toToken(ParRi, 0'u32, info)

proc addParLe*(dest: var TokenBuf; tag: TagId; info = NoLineInfo) =
  dest.add toToken(ParLe, tag, info)

proc addParRi*(dest: var TokenBuf) =
  dest.add toToken(ParRi, 0'u32, NoLineInfo)

proc addDotToken*(dest: var TokenBuf) =
  dest.add toToken(DotToken, 0'u32, NoLineInfo)

proc span*(c: Cursor): int =
  result = 0
  var c = c
  if c.kind == ParLe:
    var nested = 0
    while true:
      inc c
      inc result
      if c.kind == ParRi:
        if nested == 0: break
        dec nested
      elif c.kind == ParLe: inc nested
  if c.rem > 0:
    inc c
    inc result

proc insert*(dest: var TokenBuf; src: openArray[PackedToken]; pos: int) =
  var j = len(dest) - 1
  var i = j + len(src)
  dest.grow(i + 1)

  # Move items after `pos` to the end of the sequence.
  while j >= pos:
    dest[i] = dest[j]
    dec i
    dec j
  # Insert items from `dest` into `dest` at `pos`
  inc j
  for item in src:
    dest[j] = item
    inc j

proc insert*(dest: var TokenBuf; src: Cursor; pos: int) =
  insert dest, toOpenArray(cast[ptr  UncheckedArray[PackedToken]](src.p), 0, span(src)-1), pos

proc replace*(dest: var TokenBuf; by: Cursor; pos: int) =
  let len = span(Cursor(p: addr dest.data[pos], rem: dest.len-pos))
  let actualLen = min(len, dest.len - pos)
  let byLen = span(by)
  let oldLen = dest.len
  let newLen = oldLen + byLen - actualLen
  if byLen > actualLen:
    # Need to make room for additional elements
    dest.grow(newLen)
    # Move existing elements to the right
    for i in countdown(oldLen - 1, pos + actualLen):
      dest[i + byLen - actualLen] = dest[i]
  elif byLen < actualLen:
    # Need to remove elements
    for i in pos + byLen ..< dest.len - (actualLen - byLen):
      dest[i] = dest[i + actualLen - byLen]
    dest.shrink(newLen)
  # Copy new elements
  var by = by
  for i in 0 ..< byLen:
    dest[pos + i] = by.load
    inc by

proc toString*(b: TokenBuf; produceLineInfo = true): string =
  result = nifstreams.toString(toOpenArray(b.data, 0, b.len-1), produceLineInfo)

proc toString*(b: Cursor; produceLineInfo = true): string =
  let counter = span(b)
  result = nifstreams.toString(toOpenArray(cast[ptr UncheckedArray[PackedToken]](b.p), 0, counter-1), produceLineInfo)

proc `$`*(c: Cursor): string = toString(c, false)

proc addToken[L](tree: var TokenBuf; kind: TokenKind; id: L; info: PackedLineInfo) =
  tree.add toToken(kind, id, info)

template copyInto*(dest: var TokenBuf; tag: TagId; info: PackedLineInfo; body: untyped) =
  dest.addToken ParLe, tag, info
  body
  dest.addToken ParRi, 0'u32, info

template copyIntoUnchecked*(dest: var TokenBuf; tag: string; info: PackedLineInfo; body: untyped) =
  dest.addToken ParLe, pool.tags.getOrIncl(tag), info
  body
  dest.addToken ParRi, 0'u32, info

proc parse*(r: var Stream; dest: var TokenBuf;
            parentInfo: PackedLineInfo): bool =
  r.parents[0] = parentInfo
  while true:
    let tok = r.next()
    dest.add tok
    if tok.kind == EofToken: break
