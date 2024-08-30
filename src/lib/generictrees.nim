#       Nif library
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Parse NIF into a packed tree representation.

import bitabs, lineinfos, stringviews, packedtrees, nifreader, nifbuilder

type
  NifKind* = enum
    Empty, Ident, Sym, Symdef, IntLit, UIntLit, FloatLit, CharLit, StrLit,
    Tag,
    Err, # must not be an atom!
    Suffixed,
    Other

type
  StrId* = distinct uint32
  IntId* = distinct uint32
  UIntId* = distinct uint32
  FloatId* = distinct uint32
  TagId* = distinct uint32
  Literals* = object
    man*: LineInfoManager
    tags*: BiTable[TagId, string]
    files*: BiTable[FileId, string] # we cannot use StringView here as it may have unexpanded backslashes!
    strings*: BiTable[StrId, string]
    integers*: BiTable[IntId, int64]
    uintegers*: BiTable[UIntId, uint64]
    floats*: BiTable[FloatId, float64]

proc `==`*(a, b: StrId): bool {.borrow.}
proc `==`*(a, b: IntId): bool {.borrow.}
proc `==`*(a, b: UIntId): bool {.borrow.}
proc `==`*(a, b: FloatId): bool {.borrow.}
proc `==`*(a, b: TagId): bool {.borrow.}

proc addAtom*[L](dest: var PackedTree[NifKind]; kind: NifKind; lit: L; info: PackedLineInfo) =
  packedtrees.addAtom dest, kind, uint32(lit), info

const
  LastTag = 255'u32

proc parse*(r: var Reader; dest: var PackedTree[NifKind]; lits: var Literals;
            parentInfo: PackedLineInfo): bool =
  let t = next(r)
  var currentInfo = parentInfo
  if t.filename.len == 0:
    # relative file position
    if t.pos.line != 0 or t.pos.col != 0:
      let (file, line, col) = unpack(lits.man, parentInfo)
      currentInfo = pack(lits.man, file, line+t.pos.line, col+t.pos.col)
  else:
    # absolute file position:
    let fileId = lits.files.getOrIncl(decodeFilename t)
    currentInfo = pack(lits.man, fileId, t.pos.line, t.pos.col)

  result = true
  case t.tk
  of EofToken, ParRi:
    result = false
  of ParLe:
    #let kind = whichKind(t.s, Err)
    let ka = lits.tags.getOrInclFromView(t.s).uint32 + ord(Other).uint32
    let kb = if ka > LastTag: ord(Other).uint32 else: ka
    copyInto(dest, cast[NifKind](kb), currentInfo):
      if ka > LastTag:
        # handle overflow:
        dest.addAtom Tag, ka, currentInfo
      while true:
        let progress = parse(r, dest, lits, currentInfo)
        if not progress: break

  of UnknownToken:
    copyInto dest, Err, currentInfo:
      dest.addAtom StrLit, lits.strings.getOrIncl(decodeStr t), currentInfo
  of DotToken:
    dest.addAtom Empty, 0'u32, currentInfo
  of Ident:
    dest.addAtom Ident, lits.strings.getOrIncl(decodeStr t), currentInfo
  of Symbol:
    dest.addAtom Sym, lits.strings.getOrIncl(decodeStr t), currentInfo
  of SymbolDef:
    dest.addAtom Symdef, lits.strings.getOrIncl(decodeStr t), currentInfo
  of CharLit:
    dest.addAtom CharLit, uint32 decodeChar(t), currentInfo
  of StringLit:
    dest.addAtom StrLit, lits.strings.getOrIncl(decodeStr t), currentInfo
  of IntLit:
    dest.addAtom IntLit, lits.integers.getOrIncl(decodeInt t), currentInfo
  of UIntLit:
    dest.addAtom UIntLit, lits.uintegers.getOrIncl(decodeUInt t), currentInfo
  of FloatLit:
    dest.addAtom FloatLit, lits.floats.getOrIncl(decodeFloat t), currentInfo

type
  Tree* = PackedTree[NifKind]
  Node* = PackedNode[NifKind]

proc litId*(n: Node): StrId {.inline.} =
  assert n.kind in {Ident, Sym, Symdef, StrLit}
  StrId(n.uoperand)

proc intId*(n: Node): IntId {.inline.} =
  assert n.kind == IntLit
  IntId(n.uoperand)

proc uintId*(n: Node): UIntId {.inline.} =
  assert n.kind == UIntLit
  UIntId(n.uoperand)

proc floatId*(n: Node): FloatId {.inline.} =
  assert n.kind == FloatLit
  FloatId(n.uoperand)

proc tagId*(n: Node): TagId {.inline.} =
  assert n.kind == Tag, $n.kind
  TagId(n.uoperand)

#proc tagAsStr*(n: )

proc tag*(tree: Tree; n: NodePos): TagId =
  let k = tree[n].kind
  if k == Other:
    assert hasAtLeastXsons(tree, n, 1)
    result = tree[n.firstSon].tagId
  else:
    result = cast[TagId](k)

proc toString(b: var Builder; tree: Tree; n: NodePos; lits: Literals) =
  let k = tree[n].kind
  case k
  of Empty:
    b.addEmpty()
  of Ident:
    b.addIdent(lits.strings[tree[n].litId])
  of Sym:
    b.addSymbol(lits.strings[tree[n].litId])
  of Suffixed:
    let (val, suf) = sons2(tree, n)
    if tree[suf].kind == StrLit:
      case tree[val].kind
      of StrLit:
        b.addStrLit(lits.strings[tree[val].litId], lits.strings[tree[suf].litId])
      of IntLit:
        b.addIntLit(lits.integers[tree[val].intId], lits.strings[tree[suf].litId])
      of UIntLit:
        b.addUIntLit(lits.uintegers[tree[val].uintId], lits.strings[tree[suf].litId])
      of FloatLit:
        b.addFloatLit(lits.floats[tree[val].floatId], lits.strings[tree[suf].litId])
      else:
        b.addIdent "<wrong Suffixed node (first child)>"
    else:
      b.addIdent "<wrong Suffixed node (second child)>"
  of IntLit:
    b.addIntLit(lits.integers[tree[n].intId])
  of UIntLit:
    b.addUIntLit(lits.uintegers[tree[n].uintId])
  of FloatLit:
    b.addFloatLit(lits.floats[tree[n].floatId])
  of Symdef:
    b.addSymbolDef(lits.strings[tree[n].litId])
  of CharLit:
    b.addCharLit char(tree[n].uoperand)
  of StrLit:
    b.addStrLit(lits.strings[tree[n].litId])
  of Tag:
    b.addIdent(lits.tags[tree[n].tagId])
  else:
    if k == Other:
      assert hasAtLeastXsons(tree, n, 1)
      b.withTree lits.tags[tree[n.firstSon].tagId]:
        for ch in sonsFromX(tree, n):
          toString b, tree, ch, lits
    else:
      let tagId = cast[TagId](k)
      b.withTree lits.tags[tagId]:
        for ch in sons(tree, n):
          toString b, tree, ch, lits

proc toString*(tree: Tree; n: NodePos; lits: Literals): string =
  var b = nifbuilder.open(tree.len * 20)
  toString b, tree, n, lits
  result = b.extract()


type
  Module* = object
    t*: PackedTree[NifKind]
    lits*: Literals

proc parse*(r: var Reader): Module =
  # empirically, (size div 7) is a good estimate for the number of nodes
  # in the file:
  result = Module(t: createPackedTree[NifKind](r.fileSize div 7))
  discard parse(r, result.t, result.lits, NoLineInfo)

proc memSizes*(m: Module) =
  echo "Tree ", m.t.len # * sizeof(PackedNode[NifKind])
  echo "Man ", m.lits.man.memSize
  echo "Tags ", m.lits.tags.memSize
  echo "Files ", m.lits.files.memSize
  echo "Strings ", m.lits.strings.memSize
  echo "Ints ", m.lits.integers.memSize
  echo "UInts ", m.lits.uintegers.memSize
  echo "Floats ", m.lits.floats.memSize
