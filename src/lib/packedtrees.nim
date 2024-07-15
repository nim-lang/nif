#       Nif library
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Packed trees for NIF dialects. The dialect is represented as generic parameter `E`
## that must be resolved to an enum. The enum has 2 requirements:
## 1. It must have a field named `Err` that is the first compound node.
## 2. It must fit in a single byte.

import std / assertions

import lineinfos

type
  NodePos* = distinct int

type
  PackedNode*[E] = object     # 8 bytes
    x: uint32
    info*: PackedLineInfo

  PackedTree*[E: enum] = object
    nodes: seq[PackedNode[E]]

proc isAtom*[E: enum](e: E): bool {.inline.} =
  mixin Err
  e < Err
proc isTree[E: enum](e: E): bool {.inline.} =
  mixin Err
  e >= Err

proc createPackedTree*[E: enum](sizeHint: int): PackedTree[E] =
  static:
    assert ord(high(E)) <= 255, "enum must fit a single byte"
  PackedTree[E](nodes: newSeqOfCap[PackedNode[E]](sizeHint))

const
  NodeKindBits = 8'u32
  NodeKindMask = (1'u32 shl NodeKindBits) - 1'u32

template kind*[E](n: PackedNode[E]): E = cast[E](n.x and NodeKindMask)
template uoperand*[E](n: PackedNode[E]): uint32 = (n.x shr NodeKindBits)
template soperand*[E](n: PackedNode[E]): int32 = cast[int32](uoperand(n))

template toX[E](k: E; operand: uint32): uint32 =
  uint32(k) or (operand shl NodeKindBits)

#template toX(k: UntypedNodeKind; operand: int32): uint32 =
#  uint32(k) or (cast[uint32](operand) shl NodeKindBits)

proc `==`*(a, b: NodePos): bool {.borrow.}

proc addAtom*[E](tree: var PackedTree; kind: E; id: uint32; info: PackedLineInfo) =
  tree.nodes.add PackedNode[E](x: toX(kind, uint32(id)), info: info)

proc isAtom*[E](tree: PackedTree[E]; pos: int): bool {.inline.} =
  tree.nodes[pos].kind.isAtom

type
  PatchPos = distinct int

proc prepare*[E](tree: var PackedTree[E]; kind: E; info: PackedLineInfo): PatchPos =
  result = PatchPos tree.nodes.len
  tree.nodes.add PackedNode[E](x: toX(kind, 0'u32), info: info)

proc prepare*[E](dest: var PackedTree[E]; source: PackedTree[E]; sourcePos: NodePos): PatchPos =
  result = PatchPos dest.nodes.len
  dest.nodes.add source.nodes[sourcePos.int]

proc patch*[E](tree: var PackedTree[E]; pos: PatchPos) =
  let pos = pos.int
  let k = tree.nodes[pos].kind
  assert not k.isAtom
  let distance = int32(tree.nodes.len - pos)
  assert distance > 0
  tree.nodes[pos].x = toX(k, cast[uint32](distance))

proc len*[E](tree: PackedTree[E]): int {.inline.} = tree.nodes.len

proc `[]`*[E](tree: PackedTree[E]; i: NodePos): lent PackedNode[E] {.inline.} =
  tree.nodes[i.int]

template rawSpan[E](n: PackedNode[E]): int = int(uoperand(n))

proc nextChild[E](tree: PackedTree[E]; pos: var int) {.inline.} =
  if tree.nodes[pos].kind.isTree:
    assert tree.nodes[pos].uoperand > 0
    inc pos, tree.nodes[pos].rawSpan
  else:
    inc pos

iterator sons*[E](tree: PackedTree[E]; n: NodePos): NodePos =
  var pos = n.int
  assert tree.nodes[pos].kind.isTree
  let last = pos + tree.nodes[pos].rawSpan
  inc pos
  while pos < last:
    yield NodePos pos
    nextChild tree, pos

iterator sons*[E](dest: var PackedTree[E]; tree: PackedTree[E]; n: NodePos): NodePos =
  let patchPos = prepare(dest, tree, n)
  for x in sons(tree, n): yield x
  patch dest, patchPos

iterator isons*[E](dest: var PackedTree[E]; tree: PackedTree[E];
                n: NodePos): (int, NodePos) =
  var i = 0
  for ch0 in sons(dest, tree, n):
    yield (i, ch0)
    inc i

iterator sonsFromX*[E](tree: PackedTree[E]; n: NodePos; x = 1): NodePos =
  var pos = n.int
  assert tree.nodes[pos].kind.isTree
  let last = pos + tree.nodes[pos].rawSpan
  inc pos
  var x = x
  while pos < last:
    if x == 0:
      yield NodePos pos
    else:
      dec x
    nextChild tree, pos

iterator sonsWithoutLastX*[E](tree: PackedTree[E]; n: NodePos; x = 1): NodePos =
  var count = 0
  for child in sons(tree, n):
    inc count
  var pos = n.int
  assert tree.nodes[pos].kind.isTree
  let last = pos + tree.nodes[pos].rawSpan
  inc pos
  while pos < last and count > x:
    yield NodePos pos
    dec count
    nextChild tree, pos

proc hasXsons*[E](tree: PackedTree[E]; n: NodePos; x: int): bool =
  var count = 0
  if tree.nodes[n.int].kind.isTree:
    for child in sons(tree, n): inc count
  result = count == x

proc hasAtLeastXsons*[E](tree: PackedTree[E]; n: NodePos; x: int): bool =
  if tree.nodes[n.int].kind.isTree:
    var count = 0
    for child in sons(tree, n):
      inc count
      if count >= x: return true
  return false

proc firstSon*[E](tree: PackedTree[E]; n: NodePos): NodePos {.inline.} =
  assert tree[n].kind.isTree
  assert n.int <= int(n) + tree[n].rawSpan
  NodePos(n.int+1)

template check[E](a: int; tree: PackedTree[E]; n: NodePos) =
  assert a  < int(n) + int(n) + tree[n].rawSpan

proc kind*[E](tree: PackedTree[E]; n: NodePos): E {.inline.} =
  tree.nodes[n.int].kind

proc info*[E](tree: PackedTree[E]; n: NodePos): PackedLineInfo {.inline.} =
  tree.nodes[n.int].info

proc span*[E](tree: PackedTree[E]; pos: int): int {.inline.} =
  if isAtom(tree, pos): 1 else: tree.nodes[pos].rawSpan

proc sons2*[E](tree: PackedTree[E]; n: NodePos): (NodePos, NodePos) =
  assert(not isAtom(tree, n.int))
  let a = n.int+1
  check a, tree, n
  let b = a + span(tree, a)
  check b, tree, n
  result = (NodePos a, NodePos b)

proc sons3*[E](tree: PackedTree[E]; n: NodePos): (NodePos, NodePos, NodePos) =
  assert(not isAtom(tree, n.int))
  let a = n.int+1
  check a, tree, n
  let b = a + span(tree, a)
  check b, tree, n
  let c = b + span(tree, b)
  check c, tree, n
  result = (NodePos a, NodePos b, NodePos c)

proc sons4*[E](tree: PackedTree[E]; n: NodePos): (NodePos, NodePos, NodePos, NodePos) {.inline.} =
  assert(not isAtom(tree, n.int))
  let a = n.int+1
  check a, tree, n
  let b = a + span(tree, a)
  check b, tree, n
  let c = b + span(tree, b)
  check c, tree, n
  let d = c + span(tree, c)
  check d, tree, n
  result = (NodePos a, NodePos b, NodePos c, NodePos d)

proc sons5*[E](tree: PackedTree[E]; n: NodePos): (NodePos, NodePos, NodePos, NodePos, NodePos) {.inline.} =
  assert(not isAtom(tree, n.int))
  let a = n.int+1
  check a, tree, n
  let b = a + span(tree, a)
  check b, tree, n
  let c = b + span(tree, b)
  check c, tree, n
  let d = c + span(tree, c)
  check d, tree, n
  let e = d + span(tree, d)
  check e, tree, n
  result = (NodePos a, NodePos b, NodePos c, NodePos d, NodePos e)

proc ithSon*[E](tree: PackedTree[E]; n: NodePos; i: int): NodePos =
  result = default(NodePos)
  if tree.nodes[n.int].kind.isTree:
    var count = 0
    for child in sons(tree, n):
      if count == i: return child
      inc count
  assert false, "node has no i-th child"

const
  StartPos* = NodePos(0)

proc firstSon*(n: NodePos): NodePos {.inline.} = NodePos(n.int+1)

proc currentPos*[E](tree: PackedTree[E]): NodePos {.inline.} = NodePos(tree.nodes.len)

template copyIntoFrom*(dest, n, body) =
  let patchPos = prepare(dest, tree, n)
  body
  patch dest, patchPos

template copyInto*(dest, kind, info, body) =
  let patchPos = prepare(dest, kind, info)
  body
  patch dest, patchPos

iterator allNodes*[E](tree: PackedTree[E]): NodePos =
  var p = 0
  while p < tree.len:
    yield NodePos(p)
    let s = span(tree, p)
    inc p, s
