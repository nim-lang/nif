#       Nif library
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Combine packed trees with a link structure for more flexibility.

import arenas, packedtrees, generictrees

type
  LinkedNode* {.acyclic.} = object
    p: NodePos
    a: Node
    down, next: ptr LinkedNode
  LinkedNodeRef = ptr LinkedNode

var nodeAlloc = createArena[LinkedNode]()

proc newNode*(): LinkedNodeRef =
  result = nodeAlloc.new[:LinkedNode]()
  result.down = nil
  result.next = nil

proc copyTree*(dest: var Tree; t: Tree; n: LinkedNode) =
  if n.p != NodePos(0):
    copyTree dest, t, n.p
  elif isAtom(n.a.kind):
    dest.copyNode n.a
  else:
    let k = n.a.kind
    copyInto dest, k, n.a.info:
      if k == Other:
        # handle overflow:
        dest.addAtom Tag, n.a.uoperand, n.a.info
      var it {.cursor.} = n.down
      while it != nil:
        copyTree(dest, t, it[])
        it = it.next

proc firstSon*(t: Tree; n: LinkedNode): LinkedNode =
  if n.p != NodePos(0):
    if t[n.p].kind == Other:
      result = LinkedNode(p: n.p.firstSon.firstSon)
    else:
      result = LinkedNode(p: n.p.firstSon)
  else:
    result = n.down[]

proc nextSon*(t: Tree; n: LinkedNode): LinkedNode =
  if n.p != NodePos(0):
    var p = n.p
    if t[p].kind == Other:
      p = p.firstSon
    next t, p
    result = LinkedNode(p: p)
  else:
    result = n.next[]

proc hasFirst*(t: Tree; n: LinkedNode): bool =
  if n.p != NodePos(0):
    result = hasFirst(t, n.p)
  else:
    result = n.down != nil

proc hasNext*(t: Tree; parent, n: LinkedNode): bool =
  if parent.p != NodePos(0):
    assert n.p != NodePos(0)
    result = hasNext(t, parent.p, n.p)
  else:
    result = n.next != nil

proc wrap*(head: var LinkedNode; tail: LinkedNode) =
  var child = newNode()
  child[] = tail
  var it = head.down
  if it == nil:
    head.down = child
  else:
    while it.next != nil:
      it = it.next
    it.next = child

proc tag*(tree: Tree; n: LinkedNode): TagId =
  if n.p != NodePos(0):
    result = tag(tree, n.p)
  elif n.a.kind == Other:
    result = TagId(n.a.uoperand)
  else:
    result = cast[TagId](n.a.kind)

proc atom*(a: Node): LinkedNode =
  result = LinkedNode(p: NodePos(0), a: a)
  #if a.k == Other:

proc createEmpty*(): LinkedNode =
  result = LinkedNode(p: NodePos(0), a: createAtom(Empty))

proc fromTreeAppend*(t: Tree): LinkedNode =
  LinkedNode(p: NodePos(t.len))

type
  Local* = object
    name*, ex*, pragmas*, typ*, value*: LinkedNode

proc asLocal*(tree: Tree; n: LinkedNode): Local =
  assert hasFirst(tree, n)
  let a = firstSon(tree, n)
  let b = nextSon(tree, a)
  let c = nextSon(tree, b)
  let d = nextSon(tree, c)
  let e = nextSon(tree, d)
  result = Local(name: a, ex: b, pragmas: c, typ: d, value: e)

type
  TypeDeclaration* = object
    name*, ex*, pragmas*, generics*, body*: LinkedNode

proc asTypeDeclaration*(tree: Tree; n: LinkedNode): TypeDeclaration =
  assert hasFirst(tree, n)
  let a = firstSon(tree, n)
  let b = nextSon(tree, a)
  let c = nextSon(tree, b)
  let d = nextSon(tree, c)
  let e = nextSon(tree, d)
  result = TypeDeclaration(name: a, ex: b, pragmas: c, generics: d, body: e)

type
  Routine* = object
    name*, ex*, pat*, generics*, retType*, params*, pragmas*, exc*, body*: LinkedNode

proc asRoutine*(tree: Tree; n: LinkedNode): Routine =
  assert hasFirst(tree, n)
  let a = firstSon(tree, n)
  let b = nextSon(tree, a)
  let c = nextSon(tree, b)
  let d = nextSon(tree, c)
  let e = nextSon(tree, d)
  let f = nextSon(tree, e)
  let g = nextSon(tree, f)
  let h = nextSon(tree, g)
  let i = nextSon(tree, h)
  result = Routine(name: a, ex: b, pat: c, generics: d,
                   retType: e, params: f, pragmas: g, exc: h, body: i)
