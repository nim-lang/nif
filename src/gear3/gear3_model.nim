#
#
#           Gear3 Compiler
#        (c) Copyright 2024 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

import std / assertions
include nifprelude
import stringviews, keymatcher

type
  StmtKind* = enum
    NoStmt
    StmtsS = "stmts"
    VarS = "var"
    LetS = "let"
    CursorS = "cursor"
    ConstS = "const"
    EmitS = "emit"
    AsgnS = "asgn"
    BlockS = "block"
    IfS = "if"
    BreakS = "break"
    WhileS = "while"
    CaseS = "case"
    RetS = "ret"
    YieldS = "yld"
    ProcS = "proc"
    FuncS = "func"
    IterS = "iter"
    ConverterS = "converter"
    MethodS = "method"
    MacroS = "macro"
    TemplateS = "template"
    TypeS = "type"

  ExprKind* = enum
    NoExpr
    AtX = "at"
    DerefX = "deref"
    DotX = "dot"
    PatX = "pat"
    ParX = "par"
    AddrX = "addr"
    NilX = "nil"
    FalseX = "false"
    TrueX = "true"
    AndX = "and"
    OrX = "or"
    NotX = "not"
    NegX = "neg"
    SizeofX = "sizeof"
    OconstrX = "oconstr"
    AconstrX = "aconstr"
    KvX = "kv"
    AddX = "add"
    SubX = "sub"
    MulX = "mul"
    DivX = "div"
    ModX = "mod"
    ShrX = "shr"
    ShlX = "shl"
    BitandX = "bitand"
    BitorX = "bitor"
    BitxorX = "bitxor"
    BitnotX = "bitnot"
    EqX = "eq"
    NeqX = "neq"
    LeX = "le"
    LtX = "lt"
    CastX = "cast"
    ConvX = "conv"
    CallX = "call"
    InfX = "inf"
    NegInfX = "neginf"
    NanX = "nan"
    SufX = "suf"
    RangeX = "range"
    RangesX = "ranges"

  TypeKind* = enum
    UnionT = "union"
    ObjectT = "object"
    EnumT = "enum"
    ProctypeT = "proctype"
    IntT = "i"
    UIntT = "u"
    FloatT = "f"
    CharT = "c"
    BoolT = "bool"
    VoidT = "void"
    PtrT = "ptr"
    ArrayT = "array"
    FlexarrayT = "flexarray"
    APtrT = "aptr"
    TypeT = "type"
    AttrT = "attr"
    VarargsT = "varargs"

  PragmaKind* = enum
    NoPragma
    ImportC = "importc"
    ImportCpp = "importcpp"
    ExportC = "exportc"
    Nodecl = "nodecl"
    Header = "header"
    Align = "align"
    Bits = "bits"
    Selectany = "selectany"
    Threadvar = "threadvar"
    Globalvar = "global"
    CompileTime = "compiletime"

  SubstructureKind* = enum
    NoSub
    ElifS = "elif"
    ElseS = "else"
    OfS = "of"
    ParamS = "param"
    ParamsS = "params"
    FldS = "fld"
    EfldS = "efld"
    AtomicS = "atomic"
    RoS = "ro"
    RestrictS = "restrict"
    PragmasS = "pragmas"

  CallConv* = enum
    NoCallConv
    CdeclC = "cdecl"
    StdcallC = "stdcall"
    SafecallC = "safecall"
    SyscallC = "syscall"
    FastcallC = "fastcall"
    ThiscallC = "thiscall"
    NoconvC = "noconv"
    MemberC = "member"
    InlineC = "inline"
    NoinlineC = "noinline"

declareMatcher parseStmtKind, StmtKind

proc stmtKind*(c: Cursor): StmtKind {.inline.} =
  assert c.kind == ParLe
  parseStmtKind pool.tags[tag(c)]

declareMatcher parsePragmaKind, PragmaKind

proc pragmaKind*(c: Cursor): PragmaKind {.inline.} =
  assert c.kind == ParLe
  parsePragmaKind pool.tags[tag(c)]

declareMatcher parseSubstructureKind, SubstructureKind

proc substructureKind*(c: Cursor): SubstructureKind {.inline.} =
  if c.kind == ParLe:
    result = parseSubstructureKind pool.tags[tag(c)]
  else:
    result = NoSub
