#       Nif library
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Cursors into token streams. Suprisingly effective even for more complex algorithms.

import std / assertions
import nifstreams, lineinfos

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
proc `=destroy`(dest: TokenBuf) {.inline.} =
  #assert dest.readers == 0, "TokenBuf still in use by some reader"
  if dest.data != nil: dealloc(dest.data)

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
        if nested == 0: break
        dec nested
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

template buildTree*(dest: var TokenBuf; tag: TagId; info: PackedLineInfo; body: untyped) =
  dest.add toToken(ParLe, tag, info)
  body
  dest.add toToken(ParRi, 0'u32, info)

proc addParLe*(dest: var TokenBuf; tag: TagId; info = NoLineInfo) =
  dest.add toToken(ParLe, tag, info)

proc addParRi*(dest: var TokenBuf) =
  dest.add toToken(ParRi, 0'u32, NoLineInfo)

proc toString*(b: TokenBuf): string =
  result = nifstreams.toString(toOpenArray(b.data, 0, b.len-1))

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
  inc c
  inc result

proc toString*(b: Cursor): string =
  let counter = span(b)
  result = nifstreams.toString(toOpenArray(cast[ptr UncheckedArray[PackedToken]](b.p), 0, counter-1))
