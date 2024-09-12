#       Nif library
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Parse NIF into a packed tree representation.

import std / [hashes, tables, strutils]
import "../lib" / [bitabs, lineinfos, stringviews, packedtrees, nifreader, keymatcher,
  nifbuilder]

type
  NifcKind* = enum
    Empty, Ident, Sym, SymDef, IntLit, UIntLit, FloatLit, CharLit, StrLit,
    Err, # must not be an atom!
    AtC = "at"
    DerefC = "deref"
    DotC = "dot"
    PatC = "pat"
    ParC = "par"
    AddrC = "addr"
    NilC = "nil"
    FalseC = "false"
    TrueC = "true"
    AndC = "and"
    OrC = "or"
    NotC = "not"
    NegC = "neg"
    SizeofC = "sizeof"
    OconstrC = "oconstr"
    AconstrC = "aconstr"
    KvC = "kv"
    AddC = "add"
    SubC = "sub"
    MulC = "mul"
    DivC = "div"
    ModC = "mod"
    ShrC = "shr"
    ShlC = "shl"
    BitandC = "bitand"
    BitorC = "bitor"
    BitxorC = "bitxor"
    BitnotC = "bitnot"
    EqC = "eq"
    NeqC = "neq"
    LeC = "le"
    LtC = "lt"
    CastC = "cast"
    ConvC = "conv"
    CallC = "call"
    RangeC = "range"
    RangesC = "ranges"
    VarC = "var"
    GvarC = "gvar"
    TvarC = "tvar"
    ConstC = "const"
    EmitC = "emit"
    AsgnC = "asgn"
    IfC = "if"
    ElifC = "elif"
    ElseC = "else"
    BreakC = "break"
    WhileC = "while"
    CaseC = "case"
    OfC = "of"
    LabC = "lab"
    JmpC = "jmp"
    RetC = "ret"
    StmtsC = "stmts"
    ParamC = "param"
    ParamsC = "params"
    ProcC = "proc"
    FldC = "fld"
    UnionC = "union"
    ObjectC = "object"
    EfldC = "efld"
    EnumC = "enum"
    ProctypeC = "proctype"
    AtomicC = "atomic"
    RoC = "ro"
    RestrictC = "restrict"
    IntC = "i"
    UIntC = "u"
    FloatC = "f"
    CharC = "c"
    BoolC = "bool"
    VoidC = "void"
    PtrC = "ptr"
    ArrayC = "array"
    FlexarrayC = "flexarray"
    APtrC = "aptr"
    TypeC = "type"
    CdeclC = "cdecl"
    StdcallC = "stdcall"
    SafecallC = "safecall"
    SyscallC = "syscall"
    FastcallC = "fastcall"
    ThiscallC = "thiscall"
    NoconvC = "noconv"
    MemberC = "member"
    AttrC = "attr"
    InlineC = "inline"
    NoinlineC = "noinline"
    VarargsC = "varargs"
    WasC = "was"
    SelectanyC = "selectany"
    PragmasC = "pragmas"
    AlignC = "align"
    BitsC = "bits"
    VectorC = "vector"
    ImpC = "imp"
    NodeclC = "nodecl"
    InclC = "incl"
    SufC = "suf"

const
  CallingConventions* = {CdeclC..MemberC}

declareMatcher whichNifcKeyword, NifcKind, ord(AtC)

type
  StrId* = distinct uint32

proc `==`*(a, b: StrId): bool {.borrow.}
proc hash*(a: StrId): Hash {.borrow.}

type
  Literals* = object
    man*: LineInfoManager
    files*: BiTable[FileId, string] # we cannot use StringView here as it may have unexpanded backslashes!
    strings*: BiTable[StrId, string]

  TypeGraph* = PackedTree[NifcKind]
  TypeId* = NodePos

  Tree* = PackedTree[NifcKind]

  Module* = object
    code*: Tree
    types*: TypeGraph
    defs*: Table[StrId, NodePos]
    lits*: Literals
    filename*: string

proc addAtom*[L](dest: var PackedTree[NifcKind]; kind: NifcKind; lit: L; info: PackedLineInfo) =
  packedtrees.addAtom dest, kind, uint32(lit), info

proc tracebackTypeC*(m: Module, pos: NodePos): NodePos =
  assert m.types[pos].kind in {ObjectC, UnionC, ArrayC}
  var pos = int pos
  while m.types[NodePos pos].kind != TypeC:
    dec pos
  result = NodePos pos

proc parse*(r: var Reader; dest: var PackedTree[NifcKind]; m: var Module; parentInfo: PackedLineInfo): bool =
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
    let kind = whichNifcKeyword(t.s, Err)
    var d = if kind == TypeC: addr(m.types) else: addr(dest)
    copyInto(d[], kind, currentInfo):
      while true:
        let progress = parse(r, d[], m, currentInfo)
        if not progress: break
  of UnknownToken:
    copyInto dest, Err, currentInfo:
      dest.addAtom StrLit, m.lits.strings.getOrIncl(decodeStr t), currentInfo
  of DotToken:
    dest.addAtom Empty, 0'u32, currentInfo
  of Ident:
    dest.addAtom Ident, m.lits.strings.getOrIncl(decodeStr t), currentInfo
  of Symbol:
    dest.addAtom Sym, m.lits.strings.getOrIncl(decodeStr t), currentInfo
  of SymbolDef:
    # Remember where to find this symbol:
    let litId = m.lits.strings.getOrIncl(decodeStr t)
    m.defs[litId] = NodePos(int(dest.currentPos) - 1)
    dest.addAtom SymDef, litId, currentInfo
  of StringLit:
    dest.addAtom StrLit, m.lits.strings.getOrIncl(decodeStr t), currentInfo
  of CharLit:
    dest.addAtom CharLit, uint32 decodeChar(t), currentInfo
  of IntLit:
    # we keep numbers as strings because we typically don't do anything with them
    # but to pass them as they are to the C code.
    dest.addAtom IntLit, m.lits.strings.getOrIncl(decodeStr t), currentInfo
  of UIntLit:
    dest.addAtom UIntLit, m.lits.strings.getOrIncl(decodeStr t), currentInfo
  of FloatLit:
    dest.addAtom FloatLit, m.lits.strings.getOrIncl(decodeStr t), currentInfo

proc parse*(r: var Reader): Module =
  # empirically, (size div 7) is a good estimate for the number of nodes
  # in the file:
  let nodeCount = r.fileSize div 7
  result = Module(code: createPackedTree[NifcKind](nodeCount),
                  types: createPackedTree[NifcKind](60))
  result.types.copyInto StmtsC, NoLineInfo:
    discard parse(r, result.code, result, NoLineInfo)

proc load*(filename: string): Module =
  var r = nifreader.open(filename)
  discard nifreader.processDirectives(r)
  result = parse(r)
  result.filename = filename
  r.close

proc memSizes*(m: Module) =
  echo "Tree ", m.code.len + m.types.len # * sizeof(PackedNode[NifcKind])
  echo "Man ", m.lits.man.memSize
  echo "Files ", m.lits.files.memSize
  echo "Strings ", m.lits.strings.memSize

# Read helpers:

template elementType*(types: TypeGraph; n: NodePos): NodePos = n.firstSon

proc litId*(n: PackedNode[NifcKind]): StrId {.inline.} =
  assert n.kind in {Ident, Sym, SymDef, IntLit, UIntLit, FloatLit, CharLit, StrLit}
  StrId(n.uoperand)

type
  TypeDecl* = object
    name*, pragmas*, body*: NodePos

proc asTypeDecl*(types: TypeGraph; n: NodePos): TypeDecl =
  assert types[n].kind == TypeC
  let (a, b, c) = sons3(types, n)
  TypeDecl(name: a, pragmas: b, body: c)

type
  FieldDecl* = object
    name*, pragmas*, typ*: NodePos

proc asFieldDecl*(types: TypeGraph; n: NodePos): FieldDecl =
  assert types[n].kind == FldC
  let (a, b, c) = sons3(types, n)
  FieldDecl(name: a, pragmas: b, typ: c)

type
  ParamDecl* = object
    name*, pragmas*, typ*: NodePos

proc asParamDecl*(types: TypeGraph; n: NodePos): ParamDecl =
  assert types[n].kind == ParamC
  let (a, b, c) = sons3(types, n)
  ParamDecl(name: a, pragmas: b, typ: c)

type
  ProcType* = object
    params*, returnType*, pragmas*: NodePos

proc asProcType*(types: TypeGraph; n: NodePos): ProcType =
  assert types[n].kind == ProctypeC
  let (_, a, b, c) = sons4(types, n)
  ProcType(params: a, returnType: b, pragmas: c)

type
  ProcDecl* = object
    name*, params*, returnType*, pragmas*, body*: NodePos

proc asProcDecl*(t: Tree; n: NodePos): ProcDecl =
  assert t[n].kind == ProcC
  let (a, b, c, d, e) = sons5(t, n)
  ProcDecl(name: a, params: b, returnType: c, pragmas: d, body: e)

type
  VarDecl* = object
    name*, pragmas*, typ*, value*: NodePos

proc asVarDecl*(t: Tree; n: NodePos): VarDecl =
  assert t[n].kind == VarC
  let (a, b, c, d) = sons4(t, n)
  VarDecl(name: a, pragmas: b, typ: c, value: d)

proc toString(b: var Builder; tree: PackedTree[NifcKind]; n: NodePos; m: Module) =
  case tree[n].kind
  of Empty:
    b.addEmpty()
  of Ident:
    b.addIdent(m.lits.strings[tree[n].litId])
  of Sym, IntLit, UIntLit, FloatLit:
    b.addSymbol(m.lits.strings[tree[n].litId])
  of SymDef:
    b.addSymbolDef(m.lits.strings[tree[n].litId])
  of CharLit:
    b.addCharLit char(tree[n].uoperand)
  of StrLit:
    b.addStrLit(m.lits.strings[tree[n].litId])
  else:
    b.withTree $tree[n].kind:
      for ch in sons(tree, n):
        toString b, tree, ch, m

proc toString*(tree: PackedTree[NifcKind]; n: NodePos; m: Module): string =
  var b = nifbuilder.open(20)
  toString b, tree, n, m
  result = b.extract()
