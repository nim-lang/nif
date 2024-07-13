#       Nif library
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Parse NIF into a packed tree representation.

import "../lib" / [bitabs, lineinfos, stringviews, packedtrees, nifreader]

type
  NifcKind* = enum
    Empty, Ident, Sym, Symdef, IntLit, UIntLit, FloatLit, CharLit, StrLit,
    Err, # must not be an atom!
    DerefC = "deref"
    AtC = "at"
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

type
  StrId* = distinct uint32
  IntId* = distinct uint32
  UIntId* = distinct uint32
  FloatId* = distinct uint32
  KindId* = distinct uint32
  Literals* = object
    man*: LineInfoManager
    kinds*: BiTable[KindId, string]
    files*: BiTable[FileId, string] # we cannot use StringView here as it may have unexpanded backslashes!
    strings*: BiTable[StrId, string]
    integers*: BiTable[IntId, int64]
    uintegers*: BiTable[UIntId, uint64]
    floats*: BiTable[FloatId, float64]

proc addAtom*[L](dest: var PackedTree[NifcKind]; kind: NifcKind; lit: L; info: PackedLineInfo) =
  packedtrees.addAtom dest, kind, uint32(lit), info

proc parse*(r: var Reader; dest: var PackedTree[NifcKind]; lits: var Literals; parentInfo: PackedLineInfo): bool =
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
    let ka = lits.kinds.getOrInclFromView(t.s).uint32 + ord(Compound).uint32
    let kb = if ka > 255'u32: ord(Compound).uint32 else: ka
    copyInto(dest, cast[NifcKind](kb), currentInfo):
      if ka > 255'u32:
        # handle overflow:
        dest.addAtom Ident, ka, currentInfo
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
  of StringLit:
    dest.addAtom StrLit, lits.strings.getOrIncl(decodeStr t), currentInfo
  of CharLit:
    dest.addAtom CharLit, uint32 decodeChar(t), currentInfo
  of IntLit:
    dest.addAtom IntLit, lits.integers.getOrIncl(decodeInt t), currentInfo
  of UIntLit:
    dest.addAtom UIntLit, lits.uintegers.getOrIncl(decodeUInt t), currentInfo
  of FloatLit:
    dest.addAtom FloatLit, lits.floats.getOrIncl(decodeFloat t), currentInfo

type
  Module* = object
    t*: PackedTree[NifcKind]
    lits*: Literals

proc parse*(r: var Reader): Module =
  # empirically, (size div 7) is a good estimate for the number of nodes
  # in the file:
  result = Module(t: createPackedTree[NifcKind](r.fileSize div 7))
  discard parse(r, result.t, result.lits, NoLineInfo)

proc memSizes*(m: Module) =
  echo "Tree ", m.t.len # * sizeof(PackedNode[NifcKind])
  echo "Man ", m.lits.man.memSize
  echo "Kinds ", m.lits.kinds.memSize
  echo "Files ", m.lits.files.memSize
  echo "Strings ", m.lits.strings.memSize
  echo "Ints ", m.lits.integers.memSize
  echo "UInts ", m.lits.uintegers.memSize
  echo "Floats ", m.lits.floats.memSize
