#       Nif library
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Combine packed trees with a link structure for more flexibility.

import arenas, packedtrees, generictrees, bitabs, lineinfos

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

proc kind*(t: Tree; n: LinkedNode): NifKind {.inline.} =
  if n.p != NodePos(0):
    result = t[n.p].kind
  else:
    result = n.a.kind

proc `[]`*(t: Tree; n: LinkedNode): Node {.inline.} =
  if n.p != NodePos(0):
    result = t[n.p]
  else:
    result = n.a

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

proc isEmpty*(n: LinkedNode): bool = n.a.kind == Empty

proc fromTreeAppend*(t: Tree): LinkedNode =
  LinkedNode(p: NodePos(t.len))

proc sons2*(tree: Tree; n: LinkedNode): (LinkedNode, LinkedNode) =
  assert hasFirst(tree, n)
  let a = firstSon(tree, n)
  let b = nextSon(tree, a)
  result = (a, b)

iterator sons*(tree: Tree; n: LinkedNode): LinkedNode =
  if hasFirst(tree, n):
    var it = firstSon(tree, n)
    while true:
      yield it
      if tree.hasNext(n, it):
        it = nextSon(tree, it)
      else:
        break

iterator sonsFromX*(tree: Tree; n: LinkedNode; x = 1): LinkedNode =
  var it = firstSon(tree, n)
  for i in 1..<x:
    it = nextSon(tree, it)
  while true:
    yield it
    if tree.hasNext(n, it):
      it = nextSon(tree, it)
    else:
      break

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

proc integralType*(lits: var Literals; head: string; bits: int64): LinkedNode =
  let tagId = lits.tags.getOrIncl(head)
  result = LinkedNode(p: NodePos(0), a: createAtom(Other, uint32 tagId))
  result.down = newNode()
  result.down[] = LinkedNode(p: NodePos(0), a: createAtom(IntLit, uint32 lits.integers.getOrIncl(bits)))

proc integralType*(lits: var Literals; head: string; mode: string): LinkedNode =
  let tagId = lits.tags.getOrIncl(head)
  result = LinkedNode(p: NodePos(0), a: createAtom(Other, uint32 tagId))
  result.down = newNode()
  result.down[] = LinkedNode(p: NodePos(0), a: createAtom(IntLit, uint32 lits.strings.getOrIncl(mode)))

type
  TreeBuilder* = object
    head, current: LinkedNodeRef
    kids: int

proc `=copy`(dest: var TreeBuilder; src: TreeBuilder) {.error.}

proc extract*(b: sink TreeBuilder): LinkedNode =
  ## Extracts the buffer from the builder.
  ## The builder should not be used afterwards.
  assert b.head != nil, "no tree constructed"
  result = move(b.head[])

proc addNode*(b: var TreeBuilder; a: Node) =
  var n = newNode()
  n[] = LinkedNode(p: NodePos(0), a: a)
  if b.head == nil: b.head = n
  if b.kids == 0:
    b.current.down = n
  else:
    b.current.next = n
  b.current = n
  inc b.kids

proc addNode*(b: var TreeBuilder; node: LinkedNode) =
  var n = newNode()
  n[] = node
  if b.head == nil: b.head = n
  if b.kids == 0:
    b.current.down = n
  else:
    b.current.next = n
  var it = n
  while it.next != nil:
    it = it.next
  b.current = it
  inc b.kids

type
  PatchNode* = distinct LinkedNodeRef

proc addTree*[T: enum](b: var TreeBuilder; lits: var Literals;
                       kind: T; info: PackedLineInfo): PatchNode =
  ## Starts a new compound node. Must be closed with `endTree`.
  ## See also `withTree`.
  let tagId = lits.tags.getOrIncl($kind)
  b.addNode createNode(Other, uint32 tagId, info)
  b.kids = 0
  result = PatchNode(b.current)

proc endTree*(b: var TreeBuilder; p: PatchNode) {.inline.} =
  b.kids = 1
  b.current = LinkedNodeRef(p)

#  ------------ Atoms ------------------------

proc addIdent*(b: var TreeBuilder; lits: var Literals; s: string; info: PackedLineInfo) =
  let id = lits.strings.getOrIncl(s)
  b.addNode createNode(Ident, uint32 id, info)

proc addSymbol*(b: var TreeBuilder; lits: var Literals; s: string; info: PackedLineInfo) =
  let id = lits.strings.getOrIncl(s)
  b.addNode createNode(Sym, uint32 id, info)

proc addSymbolDef*(b: var TreeBuilder; lits: var Literals; s: string; info: PackedLineInfo) =
  let id = lits.strings.getOrIncl(s)
  b.addNode createNode(SymDef, uint32 id, info)

proc addStrLit*(b: var TreeBuilder; lits: var Literals; s: string; info: PackedLineInfo) =
  let id = lits.strings.getOrIncl(s)
  b.addNode createNode(StrLit, uint32 id, info)

proc addEmpty*(b: var TreeBuilder; info: PackedLineInfo; count = 1) =
  for _ in 1..count:
    b.addNode createNode(Empty, 0'u32, info)

#proc addCharLit*(b: var TreeBuilder; lits: var Literals; c: char; info: PackedLineInfo) =

proc addIntLit*(b: var TreeBuilder; lits: var Literals; i: BiggestInt; info: PackedLineInfo) =
  let id = lits.integers.getOrIncl(i)
  b.addNode createNode(IntLit, uint32 id, info)

proc addUIntLit*(b: var TreeBuilder; lits: var Literals; u: BiggestUInt; info: PackedLineInfo) =
  let id = lits.uintegers.getOrIncl(u)
  b.addNode createNode(UIntLit, uint32 id, info)

proc addFloatLit*(b: var TreeBuilder; lits: var Literals; f: BiggestFloat; info: PackedLineInfo) =
  let id = lits.floats.getOrIncl(f)
  b.addNode createNode(FloatLit, uint32 id, info)

template withTree*[T: enum](b: var TreeBuilder; lits: var Literals; kind: T; info: PackedLineInfo; body: untyped) =
  ## Convenience template that wraps `body` around `addTree` and `endTree`
  ## calls.
  let patch = addTree(b, lits, kind, info)
  body
  endTree b, patch

proc addKeyw*[T: enum](b: var TreeBuilder; lits: var Literals; keyw: T; info: PackedLineInfo) =
  ## Adds a complete compound node that has no children like `(nil)`.
  withTree b, lits, keyw, info:
    discard
