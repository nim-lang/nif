#       Nif library
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Parse NIF into a packed tree representation.

import std / [hashes, tables]
import "../lib" / [bitabs, lineinfos, stringviews, packedtrees, nifreader, keymatcher]

type
  NifcKind* = enum
    Empty, Ident, Sym, Symdef, IntLit, UIntLit, FloatLit, CharLit, StrLit,
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
    SizeofC = "sizeof"
    ConstrC = "constr"
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
    ConstC = "const"
    EmitC = "emit"
    AsgnC = "asgn"
    IfC = "if"
    ElifC = "elif"
    ElseC = "else"
    WhileC = "while"
    CaseC = "case"
    OfC = "of"
    LabC = "lab"
    JmpC = "jmp"
    TjmpC = "tjmp"
    FjmpC = "fjmp"
    RetC = "ret"
    StmtsC = "stmts"
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
    AptrC = "aptr"
    TypeC = "type"
    CdeclC = "cdecl"
    StdcallC = "stdcall"
    AttrC = "attr"
    InlineC = "inline"
    VarargsC = "varargs"
    WasC = "was"
    SelectanyC = "selectany"
    PragmasC = "pragmas"
    AlignC = "align"
    TlsC = "tls"
    BitsC = "bits"
    VectorC = "vector"
    ImpC = "imp"
    InclC = "incl"

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

  Module* = object
    t*: PackedTree[NifcKind]
    types*: TypeGraph
    defs*: Table[StrId, NodePos]
    lits*: Literals

proc addAtom*[L](dest: var PackedTree[NifcKind]; kind: NifcKind; lit: L; info: PackedLineInfo) =
  packedtrees.addAtom dest, kind, uint32(lit), info

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
    m.defs[litId] = dest.currentPos
    dest.addAtom Symdef, litId, currentInfo
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
  result = Module(t: createPackedTree[NifcKind](r.fileSize div 7))
  discard parse(r, result.t, result, NoLineInfo)

proc load*(filename: string): Module =
  var r = nifreader.open(filename)
  result = parse(r)
  r.close

proc memSizes*(m: Module) =
  echo "Tree ", m.t.len # * sizeof(PackedNode[NifcKind])
  echo "Man ", m.lits.man.memSize
  echo "Files ", m.lits.files.memSize
  echo "Strings ", m.lits.strings.memSize

# Read helpers:

template elementType*(types: TypeGraph; n: NodePos): NodePos = n.firstSon

proc litId*(n: PackedNode[NifcKind]): StrId {.inline.} =
  assert n.kind in {Ident, Sym, Symdef, IntLit, UIntLit, FloatLit, CharLit, StrLit}
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
