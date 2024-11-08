#       Nimony
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Semantic checking:
## Most important task is to turn identifiers into symbols and to perform
## type checking.

import std / [tables, os, syncio]
include nifprelude
import nimony_model, symtabs, builtintypes, decls,
  programs, sigmatch

type
  TypeCursor = Cursor
  SemRoutine {.acyclic.} = ref object
    kind: SymKind
    inGeneric, inLoop, inBlock: int
    returnType: TypeCursor
    resId: SymId
    parent: SemRoutine

proc createSemRoutine(kind: SymKind; parent: SemRoutine): SemRoutine =
  result = SemRoutine(kind: kind, parent: parent, resId: SymId(0))

type
  Iface = OrderedTable[StrId, seq[SymId]] # eg. "foo" -> @["foo.1.mod", "foo.3.mod"]
  ImportedModule = object
    iface: Iface

  InstRequest* = object
    origin*: SymId
    target*: (SymId, TypeCursor)
    typeParams*: seq[TypeCursor]
    requestFrom*: seq[PackedLineInfo]

  SemContext = object
    dest: TokenBuf
    routine: SemRoutine
    currentScope: Scope
    includeStack: seq[string]
    importedModules: seq[ImportedModule]
    iface: Iface
    inBlock, inLoop, inType, inCallFn: int
    inGeneric: bool
    inGenericStack: seq[bool]
    globals, locals: Table[string, int]
    types: BuiltinTypes
    thisModuleSuffix: string

# -------------- symbol lookups -------------------------------------

template buildTree*(dest: var TokenBuf; kind: StmtKind|ExprKind|TypeKind;
                    info: PackedLineInfo; body: untyped) =
  dest.add toToken(ParLe, pool.tags.getOrIncl($kind), info)
  body
  dest.addParRi()

proc considerImportedSymbols(c: var SemContext; name: StrId; info: PackedLineInfo): int =
  result = 0
  for imported in items c.importedModules:
    let candidates = imported.iface.getOrDefault(name)
    inc result, candidates.len
    for defId in candidates:
      c.dest.add toToken(Symbol, defId, info)

proc addSymUse(dest: var TokenBuf; s: Sym; info: PackedLineInfo) =
  dest.add toToken(Symbol, s.name, info)

proc buildSymChoiceForDot(c: var SemContext; identifier: StrId; info: PackedLineInfo) =
  var count = 0
  let oldLen = c.dest.len
  c.dest.buildTree OchoiceX, info:
    var it = c.currentScope
    while it != nil:
      for sym in it.tab.getOrDefault(identifier):
        if sym.kind in {ProcY, FuncY, ConverterY, MethodY, TemplateY, MacroY, IterY, TypeY}:
          c.dest.addSymUse sym, info
          inc count
      it = it.up
    inc count, considerImportedSymbols(c, identifier, info)

  # if the sym choice is empty, create an ident node:
  if count == 0:
    c.dest.shrink oldLen
    c.dest.add toToken(Ident, identifier, info)

proc isNonOverloadable(t: SymKind): bool {.inline.} =
  t in {LetY, VarY, ParamY, TypevarY, ConstY, TypeY, ResultY, FldY, CursorY, LabelY}

proc buildSymChoiceForSelfModule(c: var SemContext;
                                 identifier: StrId; info: PackedLineInfo) =
  var count = 0
  let oldLen = c.dest.len
  c.dest.buildTree OchoiceX, info:
    var it = c.currentScope
    while it.up != nil: it = it.up
    var nonOverloadable = 0
    for sym in it.tab.getOrDefault(identifier):
      # for non-overloadable symbols prefer the innermost symbol:
      if sym.kind.isNonOverloadable:
        inc nonOverloadable
        if nonOverloadable == 1:
          c.dest.addSymUse sym, info
          inc count
      else:
        c.dest.addSymUse sym, info
        inc count
      it = it.up
  # if the sym choice is empty, create an ident node:
  if count == 0:
    c.dest.shrink oldLen
    c.dest.add toToken(Ident, identifier, info)

proc buildSymChoiceForForeignModule(c: var SemContext; importFrom: ImportedModule;
                                    identifier: StrId; info: PackedLineInfo) =
  var count = 0
  let oldLen = c.dest.len
  c.dest.buildTree OchoiceX, info:
    let candidates = importFrom.iface.getOrDefault(identifier)
    for defId in candidates:
      c.dest.add toToken(Symbol, defId, info)
      inc count
  # if the sym choice is empty, create an ident node:
  if count == 0:
    c.dest.shrink oldLen
    c.dest.add toToken(Ident, identifier, info)

type
  ChoiceOption = enum
    FindAll, InnerMost

proc rawBuildSymChoice(c: var SemContext; identifier: StrId; info: PackedLineInfo;
                       option = FindAll): int =
  result = 0
  var it = c.currentScope
  var nonOverloadable = 0
  while it != nil:
    for sym in it.tab.getOrDefault(identifier):
      # for non-overloadable symbols prefer the innermost symbol:
      if sym.kind.isNonOverloadable:
        if nonOverloadable == 0:
          c.dest.addSymUse sym, info
          inc result
        inc nonOverloadable
        if result == 1 and nonOverloadable == 1 and option == InnerMost:
          return
      else:
        c.dest.addSymUse sym, info
        inc result
    it = it.up
  inc result, considerImportedSymbols(c, identifier, info)

proc buildSymChoice(c: var SemContext; identifier: StrId; info: PackedLineInfo; option: ChoiceOption) =
  let oldLen = c.dest.len
  c.dest.buildTree OchoiceX, info:
    let count = rawBuildSymChoice(c, identifier, info, option)
  # if the sym choice is empty, create an ident node:
  if count == 0:
    c.dest.shrink oldLen
    c.dest.add toToken(Ident, identifier, info)

proc openScope(s: var SemContext) =
  s.currentScope = Scope(tab: initTable[StrId, seq[Sym]](), up: s.currentScope, kind: NormalScope)

proc closeScope(s: var SemContext) =
  s.currentScope = s.currentScope.up

proc buildErr*(c: var SemContext; info: PackedLineInfo; msg: string) =
  c.dest.buildTree ErrT, info:
    c.dest.add toToken(StringLit, pool.strings.getOrIncl(msg), info)

proc makeGlobalSym*(c: var SemContext; result: var string) =
  var counter = addr c.globals.mgetOrPut(result, -1)
  counter[] += 1
  result.add '.'
  result.addInt counter[]
  result.add '.'
  result.add c.thisModuleSuffix

proc makeLocalSym*(c: var SemContext; result: var string) =
  var counter = addr c.locals.mgetOrPut(result, -1)
  counter[] += 1
  result.add '.'
  result.addInt counter[]

type
  SymStatus = enum
    ErrNoIdent, ErrRedef, OkNew, OkExisting

  DelayedSym = object
    status: SymStatus
    lit: StrId
    s: Sym
    info: PackedLineInfo

proc identToSym(c: var SemContext; lit: StrId): SymId =
  var name = pool.strings[lit]
  if c.currentScope.kind == ToplevelScope:
    c.makeGlobalSym(name)
  else:
    c.makeLocalSym(name)
  result = pool.syms.getOrIncl(name)

proc declareSym(c: var SemContext; it: var Item): SymStatus =
  let info = it.n.info
  if it.n.kind == Ident:
    let lit = it.n.litId
    let kind = c.dest[c.dest.len-1].symKind

    let s = Sym(name: identToSym(c, lit),
                kind: kind, pos: 0'i32)
    if addNonOverloadable(c.currentScope, lit, s) == Conflict:
      c.buildErr info, "attempt to redeclare: " & pool.strings[lit]
      result = ErrRedef
    else:
      c.dest.add toToken(SymbolDef, s.name, info)
      result = Oknew
    inc it.n
  elif it.n.kind == SymbolDef:
    inc it.n
    result = OkExisting
  else:
    c.buildErr info, "identifier expected"
    result = ErrNoIdent

proc declareOverloadableSym(c: var SemContext; it: var Item): SymStatus =
  let info = it.n.info
  if it.n.kind == Ident:
    let lit = it.n.litId
    let kind = c.dest[c.dest.len-1].symKind

    let s = Sym(name: identToSym(c, lit),
                kind: kind, pos: 0'i32)
    addOverloadable(c.currentScope, lit, s)
    result = Oknew
    inc it.n
  elif it.n.kind == SymbolDef:
    result = OkExisting
  else:
    c.buildErr info, "identifier expected"
    result = ErrNoIdent

proc success(s: SymStatus): bool {.inline.} = s in {OkNew, OkExisting}
proc success(s: DelayedSym): bool {.inline.} = success s.status

proc handleSymDef(c: var SemContext; it: var Item): DelayedSym =
  let info = it.n.info
  if it.n.kind == Ident:
    let lit = it.n.litId
    let kind = c.dest[c.dest.len-1].symKind
    let def = identToSym(c, lit)
    let s = Sym(name: def,
                kind: kind, pos: 0'i32)
    result = DelayedSym(status: OkNew, lit: lit, s: s, info: info)
    c.dest.add toToken(SymbolDef, def, info)
    inc it.n
  elif it.n.kind == SymbolDef:
    discard "ok, and no need to re-add it to the symbol table"
    result = DelayedSym(status: OkExisting, info: info)
    c.dest.add it.n
    inc it.n
  else:
    c.buildErr info, "identifier expected"
    result = DelayedSym(status: ErrNoIdent, info: info)

proc addSym(c: var SemContext; s: DelayedSym) =
  if s.status == OkNew:
    if addNonOverloadable(c.currentScope, s.lit, s.s) == Conflict:
      c.buildErr s.info, "attempt to redeclare: " & pool.strings[s.lit]
    else:
      c.dest.add toToken(SymbolDef, s.lit, s.info)

# -------------------------------------------------------------------------------------------------

proc typeToString(e: var SemContext; c: Cursor): string =
  result = toString(c)

proc wantParRi(e: var SemContext; c: var Cursor) =
  if c.kind == ParRi:
    e.dest.add c
    inc c
  else:
    error "expected ')', but got: ", c

proc skipParRi(e: var SemContext; c: var Cursor) =
  if c.kind == ParRi:
    inc c
  else:
    error "expected ')', but got: ", c

proc takeToken(e: var SemContext; c: var Cursor) {.inline.} =
  e.dest.add c
  inc c

proc semExpr(e: var SemContext; it: var Item)

proc classifyType(e: var SemContext; c: Cursor): TypeKind =
  result = typeKind(c)

proc semBoolExpr(e: var SemContext; it: var Item) =
  semExpr e, it
  if typeKind(it.typ) != BoolT:
    buildErr e, it.n.info, "expected `bool` but got: " & typeToString(e, it.typ)

proc semStmt(e: var SemContext; c: var Cursor) =
  var it = Item(n: c, typ: e.types.autoType)
  semExpr e, it
  if classifyType(e, it.typ) in {NoType, VoidT}:
    discard "ok"
  else:
    buildErr e, c.info, "expression of type `" & typeToString(e, it.typ) & "` must be discarded"
  c = it.n

proc semCall(e: var SemContext; it: var Item) =
  let callNode = it.n
  var dest = createTokenBuf(16)
  swap e.dest, dest
  var fn = Item(n: it.n, typ: e.types.autoType)
  semExpr e, fn
  it.n = fn.n
  var args: seq[Item] = @[]
  while it.n.kind != ParRi:
    var arg = Item(n: it.n, typ: e.types.autoType)
    semExpr e, arg
    let next = arg.n
    arg.n = it.n
    it.n = next
    args.add arg
  var m = createMatch()
  sigmatch(m, fn, args, e.types.voidType)
  # XXX e.types.voidType is a little hack to pass DotToken to `explicitTypeVars` for now
  swap e.dest, dest
  e.dest.add callNode
  e.dest.add fn.n
  e.dest.add m.args
  wantParRi e, it.n


proc semExpr(e: var SemContext; it: var Item) =
  case it.n.kind
  of IntLit:
    if typeKind(it.typ) == AutoT:
      it.typ = e.types.intType
    takeToken e, it.n
  of UIntLit:
    if typeKind(it.typ) == AutoT:
      it.typ = e.types.uintType
    takeToken e, it.n
  of FloatLit:
    if typeKind(it.typ) == AutoT:
      it.typ = e.types.floatType
    takeToken e, it.n
  of StringLit:
    if typeKind(it.typ) == AutoT:
      it.typ = e.types.stringType
    takeToken e, it.n
  of CharLit:
    if typeKind(it.typ) == AutoT:
      it.typ = e.types.charType
    takeToken e, it.n
  of Symbol, Ident:
    buildErr e, it.n.info, "not implemented"
  of ParLe:
    case exprKind(it.n)
    of NoExpr:
      buildErr e, it.n.info, "expression expected"
    of FalseX, TrueX:
      if typeKind(it.typ) == AutoT:
        it.typ = e.types.boolType
      takeToken e, it.n
      wantParRi e, it.n
    of InfX, NegInfX, NanX:
      if typeKind(it.typ) == AutoT:
        it.typ = e.types.floatType
      takeToken e, it.n
      wantParRi e, it.n
    of AndX, OrX:
      takeToken e, it.n
      semBoolExpr e, it
      semBoolExpr e, it
      wantParRi e, it.n
    of NotX:
      e.dest.add it.n
      takeToken e, it.n
      semBoolExpr e, it
      wantParRi e, it.n
    of ParX:
      takeToken e, it.n
      semExpr e, it
      wantParRi e, it.n
    of CallX:
      semCall e, it
    of AconstrX, AtX, DerefX, DotX, PatX, AddrX, NilX, NegX, SizeofX, OconstrX, KvX,
       AddX, SubX, MulX, DivX, ModX, ShrX, ShlX, BitandX, BitorX, BitxorX, BitnotX,
       EqX, NeqX, LeX, LtX, CastX, ConvX, SufX, RangeX, RangesX,
       HderefX, HaddrX, OconvX, HconvX, OchoiceX, CchoiceX:
      takeToken e, it.n
      wantParRi e, it.n

  of ParRi, EofToken, SymbolDef, UnknownToken, DotToken:
    buildErr e, it.n.info, "expression expected"

proc writeOutput(e: var SemContext; outfile: string) =
  #var b = nifbuilder.open(outfile)
  #b.addHeader "nimony", "nim-sem"
  #b.addRaw toString(e.dest)
  #b.close()
  writeFile outfile, "(.nif42)\n" & toString(e.dest)

proc semcheck*(infile, outfile: string) =
  var c = setupProgram(infile)
  var e = SemContext(
    dest: createTokenBuf(),
    types: createBuiltinTypes(),
    thisModuleSuffix: prog.main)
  e.currentScope = Scope(tab: initTable[StrId, seq[Sym]](), up: nil, kind: ToplevelScope)

  semStmt e, c
  if c.kind != EofToken:
    quit "Internal error: file not processed completely"
  # fix point: generic instantiations:
  when false:
    var i = 0
    while i < e.requires.len:
      let imp = e.requires[i]
      if not e.declared.contains(imp):
        importSymbol(e, imp)
      inc i
  writeOutput e, outfile

