#       Nif library
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Parse NIF into a packed tree representation.

import std / [hashes, tables]
import "../lib" / [bitabs, lineinfos, stringviews, packedtrees, nifreader, keymatcher,
  nifbuilder]

type
  XelimKind* = enum
    Empty, Ident, Sym, Symdef, IntLit, UIntLit, FloatLit, CharLit, StrLit,
    Tag,   # tag of "other" compound node
    Err, # must not be an atom!
    Other, # other compound node
    TrueX = "true"
    FalseX = "false"
    BoolX = "bool"
    AutoX = "auto"
    AndX = "and"
    OrX = "or"
    TypeofX = "typeof"
    CallX = "call"
    AsgnX = "asgn"
    ExprX = "expr"
    LetX = "let"
    VarX = "var"
    CursorX = "cursor"
    ConstX = "const"

    RetX = "ret"
    DiscardX = "discard"
    RaiseX = "raise"
    YieldX = "yield"
    IfX = "if"
    ElifX = "elif"
    ElseX = "else"
    BreakX = "break"
    WhileX = "while"
    CaseX = "case"
    OfX = "of"
    TryX = "try"
    ExceptX = "except"
    FinallyX = "fin"
    ProcX = "proc"

    StmtsX = "stmts"

const
  DeclarativeNodes* = {TypeofX}
  ReturnTypePos* = 5

declareMatcher whichXelimKeyword, XelimKind, ord(TrueX)

type
  StrId* = distinct uint32

proc `==`*(a, b: StrId): bool {.borrow.}
proc hash*(a: StrId): Hash {.borrow.}

type
  TagId* = distinct uint32
  Literals* = object
    man*: LineInfoManager
    tags*: BiTable[TagId, string]
    files*: BiTable[FileId, string] # we cannot use StringView here as it may have unexpanded backslashes!
    strings*: BiTable[StrId, string]

  Tree* = PackedTree[XelimKind]
  Node* = PackedNode[XelimKind]

  Module* = object
    code*: Tree
    defs*: Table[StrId, NodePos]
    lits*: Literals

proc addAtom*[L](dest: var Tree; kind: XelimKind; lit: L; info: PackedLineInfo) =
  packedtrees.addAtom dest, kind, uint32(lit), info

proc createAtom*[L](kind: XelimKind; lit: L): Node =
  packedtrees.createAtom kind, uint32(lit)

proc parse*(r: var Reader; m: var Module; parentInfo: PackedLineInfo): bool =
  let t = next(r)
  var currentInfo = parentInfo
  if t.filename.len == 0:
    # relative file position
    if t.pos.line != 0 or t.pos.col != 0:
      let (file, line, col) = unpack(m.lits.man, parentInfo)
      currentInfo = pack(m.lits.man, file, line+t.pos.line, col+t.pos.col)
  else:
    # absolute file position:
    let fileId = m.lits.files.getOrIncl(decodeFilename t)
    currentInfo = pack(m.lits.man, fileId, t.pos.line, t.pos.col)

  result = true
  case t.tk
  of EofToken, ParRi:
    result = false
  of ParLe:
    let kind = whichXelimKeyword(t.s, Other)
    copyInto(m.code, kind, currentInfo):
      if kind == Other:
        let tag = m.lits.tags.getOrInclFromView(t.s)
        m.code.addAtom Tag, tag, currentInfo
      while true:
        let progress = parse(r, m, currentInfo)
        if not progress: break

  of UnknownToken:
    copyInto m.code, Err, currentInfo:
      m.code.addAtom StrLit, m.lits.strings.getOrIncl(decodeStr t), currentInfo
  of DotToken:
    m.code.addAtom Empty, 0'u32, currentInfo
  of Ident:
    m.code.addAtom Ident, m.lits.strings.getOrIncl(decodeStr t), currentInfo
  of Symbol:
    m.code.addAtom Sym, m.lits.strings.getOrIncl(decodeStr t), currentInfo
  of SymbolDef:
    # Remember where to find this symbol:
    let litId = m.lits.strings.getOrIncl(decodeStr t)
    m.defs[litId] = m.code.currentPos
    m.code.addAtom Symdef, litId, currentInfo
  of StringLit:
    m.code.addAtom StrLit, m.lits.strings.getOrIncl(decodeStr t), currentInfo
  of CharLit:
    m.code.addAtom CharLit, uint32 decodeChar(t), currentInfo
  of IntLit:
    # we keep numbers as strings because we don't do anything with them
    m.code.addAtom IntLit, m.lits.strings.getOrIncl(decodeStr t), currentInfo
  of UIntLit:
    m.code.addAtom UIntLit, m.lits.strings.getOrIncl(decodeStr t), currentInfo
  of FloatLit:
    m.code.addAtom FloatLit, m.lits.strings.getOrIncl(decodeStr t), currentInfo

proc parse*(r: var Reader): Module =
  # empirically, (size div 7) is a good estimate for the number of nodes
  # in the file:
  let nodeCount = r.fileSize div 7
  result = Module(code: createPackedTree[XelimKind](nodeCount))
  discard parse(r, result, NoLineInfo)

proc load*(filename: string): Module =
  var r = nifreader.open(filename)
  discard nifreader.processDirectives(r)
  result = parse(r)
  r.close

proc memSizes*(m: Module) =
  echo "Tree ", m.code.len # * sizeof(PackedNode[XelimKind])
  echo "Man ", m.lits.man.memSize
  echo "Files ", m.lits.files.memSize
  echo "Strings ", m.lits.strings.memSize

# Read helpers:

proc litId*(n: PackedNode[XelimKind]): StrId {.inline.} =
  assert n.kind in {Ident, Sym, Symdef, IntLit, UIntLit, FloatLit, CharLit, StrLit}
  StrId(n.uoperand)

proc tagId*(n: PackedNode[XelimKind]): TagId {.inline.} =
  assert n.kind == Tag, $n.kind
  TagId(n.uoperand)

type
  LocalDecl* = object
    name*, ex*, pragmas*, typ*, val*: NodePos

proc asLocalDecl*(t: Tree; n: NodePos): LocalDecl =
  assert t[n].kind in {LetX, VarX, CursorX, ConstX}
  let (a, b, c, d, e) = sons5(t, n)
  LocalDecl(name: a, ex: b, pragmas: c, typ: d, val: e)

type
  ProcDecl* = object
    name*, params*, returnType*, pragmas*, body*: NodePos

proc asProcDecl*(t: Tree; n: NodePos): ProcDecl =
  assert t[n].kind == ProcX
  let (a, b, c, d, e) = sons5(t, n)
  ProcDecl(name: a, params: b, returnType: c, pragmas: d, body: e)

proc toString(b: var Builder; tree: Tree; n: NodePos; lits: Literals) =
  case tree[n].kind
  of Empty:
    b.addEmpty()
  of Ident:
    b.addIdent(lits.strings[tree[n].litId])
  of Sym, IntLit, UIntLit, FloatLit:
    b.addSymbol(lits.strings[tree[n].litId])
  of Symdef:
    b.addSymbolDef(lits.strings[tree[n].litId])
  of CharLit:
    b.addCharLit char(tree[n].uoperand)
  of StrLit:
    b.addStrLit(lits.strings[tree[n].litId])
  of Tag:
    b.addIdent(lits.tags[tree[n].tagId])
  of Other:
    assert hasAtLeastXsons(tree, n, 1)
    b.withTree lits.tags[tree[n.firstSon].tagId]:
      for ch in sonsFromX(tree, n):
        toString b, tree, ch, lits
  else:
    b.withTree $tree[n].kind:
      for ch in sons(tree, n):
        toString b, tree, ch, lits

proc toString*(tree: Tree; n: NodePos; lits: Literals): string =
  var b = nifbuilder.open(tree.len * 20)
  toString b, tree, n, lits
  result = b.extract()
