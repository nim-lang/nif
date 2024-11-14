#       Nimony
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Semantic checking:
## Most important task is to turn identifiers into symbols and to perform
## type checking.

import std / [tables, os, syncio, formatfloat, assertions]
include nifprelude
import nimony_model, symtabs, builtintypes, decls, symparser,
  programs, sigmatch, magics, reporters

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
    instantiatedFrom: seq[PackedLineInfo]
    iface: Iface
    inBlock, inLoop, inType, inCallFn: int
    inGeneric: bool
    inGenericStack: seq[bool]
    globals, locals: Table[string, int]
    types: BuiltinTypes
    typeMem: Table[string, TokenBuf]
    thisModuleSuffix: string

# -------------- symbol lookups -------------------------------------

proc unquote(c: var Cursor): StrId =
  var r = ""
  while true:
    case c.kind
    of ParRi:
      inc c
      break
    of EofToken:
      r.add "<unexpected eof>"
      break
    of Ident, StringLit:
      r.add pool.strings[c.litId]
      inc c
    of IntLit:
      r.addInt pool.integers[c.intId]
      inc c
    of CharLit:
      let ch = char(c.uoperand)
      r.add ch
      inc c
    of UIntLit:
      r.add $pool.uintegers[c.uintId]
      inc c
    of FloatLit:
      r.addFloat pool.floats[c.floatId]
      inc c
    else:
      r.add "<unexpected token>: " & $c.kind
      inc c
  assert r.len > 0
  result = getOrIncl(pool.strings, r)

proc getIdent(c: var SemContext; n: var Cursor): StrId =
  var nested = 0
  while exprKind(n) in {OchoiceX, CchoiceX}:
    inc nested
    inc n
  case n.kind
  of Ident:
    result = n.litId
  of Symbol, SymbolDef:
    let sym = pool.syms[n.symId]
    var isGlobal = false
    result = pool.strings.getOrIncl(extractBasename(sym, isGlobal))
  of ParLe:
    if exprKind(n) == QuotedX:
      result = unquote(n)
    else:
      result = StrId(0)
  else:
    result = StrId(0)
  while nested > 0:
    if n.kind == ParRi: dec nested
    inc n

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

proc buildSymChoice(c: var SemContext; identifier: StrId; info: PackedLineInfo;
                    option: ChoiceOption): int =
  let oldLen = c.dest.len
  c.dest.buildTree OchoiceX, info:
    result = rawBuildSymChoice(c, identifier, info, option)
  # if the sym choice is empty, create an ident node:
  if result == 0:
    c.dest.shrink oldLen
    c.dest.add toToken(Ident, identifier, info)

proc openScope(c: var SemContext) =
  c.currentScope = Scope(tab: initTable[StrId, seq[Sym]](), up: c.currentScope, kind: NormalScope)

proc closeScope(c: var SemContext) =
  c.currentScope = c.currentScope.up

# -------------------------- error handling -------------------------

proc pushErrorContext(c: var SemContext; info: PackedLineInfo) = c.instantiatedFrom.add info
proc popErrorContext(c: var SemContext) = discard c.instantiatedFrom.pop

proc buildErr*(c: var SemContext; info: PackedLineInfo; msg: string) =
  c.dest.buildTree ErrT, info:
    for instFrom in items(c.instantiatedFrom):
      c.dest.add toToken(UnknownToken, 0'u32, instFrom)
    c.dest.add toToken(StringLit, pool.strings.getOrIncl(msg), info)

# -------------------------- type handling ---------------------------

proc typeToCanon(c: var SemContext; start: int): string =
  result = ""
  for i in start..<c.dest.len:
    case c.dest[i].kind
    of ParLe:
      result.add '('
      result.addInt c.dest[i].tagId.int
    of ParRi: result.add ')'
    of Ident, StringLit:
      result.add ' '
      result.addInt c.dest[i].litId.int
    of UnknownToken: result.add " unknown"
    of EofToken: result.add " eof"
    of DotToken: result.add '.'
    of Symbol, SymbolDef:
      result.add " s"
      result.addInt c.dest[i].symId.int
    of CharLit:
      result.add " c"
      result.addInt c.dest[i].uoperand.int
    of IntLit:
      result.add " i"
      result.addInt c.dest[i].intId.int
    of UIntLit:
      result.add " u"
      result.addInt c.dest[i].uintId.int
    of FloatLit:
      result.add " f"
      result.addInt c.dest[i].floatId.int

proc typeToCursor(c: var SemContext; start: int): TypeCursor =
  let key = typeToCanon(c, start)
  if c.typeMem.hasKey(key):
    result = cursorAt(c.typeMem[key], 0)
  else:
    var buf = createTokenBuf(c.dest.len - start)
    for i in start..<c.dest.len:
      buf.add c.dest[i]
    result = cursorAt(buf, 0)
    c.typeMem[key] = buf

# --------------------- symbol name creation -------------------------

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

proc declareSym(c: var SemContext; it: var Item; kind: SymKind): SymStatus =
  let info = it.n.info
  if it.n.kind == Ident:
    let lit = it.n.litId
    let s = Sym(kind: kind, name: identToSym(c, lit),
                pos: c.dest.len)
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

proc declareOverloadableSym(c: var SemContext; it: var Item; kind: SymKind) =
  let info = it.n.info
  if it.n.kind == Ident:
    let lit = it.n.litId
    let s = Sym(kind: kind, name: identToSym(c, lit),
                pos: c.dest.len)
    addOverloadable(c.currentScope, lit, s)
    c.dest.add toToken(SymbolDef, s.name, info)
    inc it.n
  elif it.n.kind == SymbolDef:
    c.dest.add it.n
    inc it.n
  else:
    let lit = getIdent(c, it.n)
    if lit == StrId(0):
      c.buildErr info, "identifier expected"
    else:
      let s = Sym(kind: kind, name: identToSym(c, lit),
                  pos: c.dest.len)
      addOverloadable(c.currentScope, lit, s)
      c.dest.add toToken(SymbolDef, s.name, info)
      inc it.n

proc success(s: SymStatus): bool {.inline.} = s in {OkNew, OkExisting}
proc success(s: DelayedSym): bool {.inline.} = success s.status

proc handleSymDef(c: var SemContext; n: var Cursor; kind: SymKind): DelayedSym =
  let info = n.info
  if n.kind == Ident:
    let lit = n.litId
    let def = identToSym(c, lit)
    let s = Sym(kind: kind, name: def,
                pos: c.dest.len)
    result = DelayedSym(status: OkNew, lit: lit, s: s, info: info)
    c.dest.add toToken(SymbolDef, def, info)
    inc n
  elif n.kind == SymbolDef:
    discard "ok, and no need to re-add it to the symbol table"
    result = DelayedSym(status: OkExisting, info: info)
    c.dest.add n
    inc n
  else:
    let lit = getIdent(c, n)
    if lit == StrId(0):
      c.buildErr info, "identifier expected"
      result = DelayedSym(status: ErrNoIdent, info: info)
    else:
      let def = identToSym(c, lit)
      let s = Sym(kind: kind, name: def,
                  pos: c.dest.len)
      result = DelayedSym(status: OkNew, lit: lit, s: s, info: info)
      c.dest.add toToken(SymbolDef, def, info)

proc addSym(c: var SemContext; s: DelayedSym) =
  if s.status == OkNew:
    if addNonOverloadable(c.currentScope, s.lit, s.s) == Conflict:
      c.buildErr s.info, "attempt to redeclare: " & pool.strings[s.lit]

# -------------------------------------------------------------------------------------------------

proc copyTree(c: var SemContext; n: var Cursor) =
  var nested = 0
  if n.kind != ParLe:
    c.dest.add n
  else:
    while true:
      c.dest.add n
      case n.kind
      of Parle: inc nested
      of ParRi:
        c.dest.add n
        if nested == 0:
          inc n
          break
        dec nested
      of EofToken:
        error "expected ')', but EOF reached"
        break
      else: discard
      inc n

# -------------------------------------------------------------

proc typeToString(c: var SemContext; n: Cursor): string =
  result = toString(n)

proc wantParRi(c: var SemContext; n: var Cursor) =
  if n.kind == ParRi:
    c.dest.add n
    inc n
  else:
    error "expected ')', but got: ", n

proc skipParRi(c: var SemContext; n: var Cursor) =
  if n.kind == ParRi:
    inc n
  else:
    error "expected ')', but got: ", n

proc takeToken(c: var SemContext; n: var Cursor) {.inline.} =
  c.dest.add n
  inc n

proc wantDot(c: var SemContext; n: var Cursor) =
  if n.kind == DotToken:
    c.dest.add n
    inc n
  else:
    buildErr c, n.info, "expected '.'"

proc semExpr(c: var SemContext; it: var Item)

proc classifyType(c: var SemContext; n: Cursor): TypeKind =
  result = typeKind(n)

proc semBoolExpr(c: var SemContext; it: var Item) =
  semExpr c, it
  if classifyType(c, it.typ) != BoolT:
    buildErr c, it.n.info, "expected `bool` but got: " & typeToString(c, it.typ)

proc semProcBody(c: var SemContext; itB: var Item) =
  #let beforeBodyPos = c.dest.len
  var it = Item(n: itB.n, typ: c.types.autoType)
  semExpr c, it
  if classifyType(c, it.typ) == VoidT:
    discard "ok"
  else:
    # XXX
    buildErr c, itB.n.info, "proc body as expression not implemented"
  itB.n = it.n

proc semStmt(c: var SemContext; n: var Cursor) =
  var it = Item(n: n, typ: c.types.autoType)
  semExpr c, it
  if classifyType(c, it.typ) in {NoType, VoidT}:
    discard "ok"
  else:
    buildErr c, n.info, "expression of type `" & typeToString(c, it.typ) & "` must be discarded"
  n = it.n

proc semCall(c: var SemContext; it: var Item) =
  let callNode = it.n
  var dest = createTokenBuf(16)
  swap c.dest, dest
  var fn = Item(n: it.n, typ: c.types.autoType)
  semExpr c, fn
  it.n = fn.n
  var args: seq[Item] = @[]
  while it.n.kind != ParRi:
    var arg = Item(n: it.n, typ: c.types.autoType)
    semExpr c, arg
    let next = arg.n
    arg.n = it.n
    it.n = next
    args.add arg
  var m = createMatch()
  sigmatch(m, fn, args, c.types.voidType)
  # XXX c.types.voidType is a little hack to pass DotToken to `explicitTypeVars` for now
  swap c.dest, dest
  c.dest.add callNode
  c.dest.add fn.n
  c.dest.add m.args
  wantParRi c, it.n

proc combineType(dest: var Cursor; src: Cursor) =
  if typeKind(dest) == AutoT:
    dest = src

proc semWhile(c: var SemContext; it: var Item) =
  c.dest.add it.n
  inc it.n
  semBoolExpr c, it
  inc c.routine.inLoop
  semStmt c, it.n
  dec c.routine.inLoop
  wantParRi c, it.n
  combineType it.typ, c.types.voidType

proc semBreak(c: var SemContext; it: var Item) =
  takeToken c, it.n
  if c.routine.inLoop+c.routine.inBlock == 0:
    buildErr c, it.n.info, "`break` only possible within a `while` or `block` statement"
  else:
    wantDot c, it.n
  wantParRi c, it.n
  combineType it.typ, c.types.voidType

proc wantExportMarker(c: var SemContext; n: var Cursor) =
  if n.kind == DotToken:
    c.dest.add n
    inc n
  elif n.kind == Ident and pool.strings[n.litId] == "x":
    if c.currentScope.kind != ToplevelScope:
      buildErr c, n.info, "only toplevel declarations can be exported"
    else:
      c.dest.add n
    inc n
  elif n.kind == ParLe:
    # export marker could have been turned into a NIF tag
    copyTree c, n
  else:
    buildErr c, n.info, "expected '.' or 'x' for an export marker"

proc patchType(c: var SemContext; typ: TypeCursor; patchPosition: int) =
  discard "XXX to implement"

type
  CrucialPragma* = object
    magic: string
    bits: int

proc semPragma(c: var SemContext; n: var Cursor; crucial: var CrucialPragma; kind: SymKind) =
  case pragmaKind(n)
  of NoPragma:
    if kind.isRoutine and callConvKind(n) != NoCallConv:
      takeToken c, n
      wantParRi c, n
    else:
      buildErr c, n.info, "expected pragma"
  of Magic:
    takeToken c, n
    if n.kind in {StringLit, Ident}:
      let m = parseMagic(pool.strings[n.litId])
      if m == mNone:
        buildErr c, n.info, "unknown `magic`"
      else:
        let (magicWord, bits) = magicToTag(m)
        crucial.magic = magicWord
        crucial.bits = bits
      takeToken c, n
    else:
      buildErr c, n.info, "`magic` pragma takes a string literal"
    wantParRi c, n
  of ImportC, ImportCpp, ExportC, Nodecl, Header, Align, Bits, Selectany,
     Threadvar, Globalvar:
    copyTree c, n

proc semPragmas(c: var SemContext; n: var Cursor; crucial: var CrucialPragma; kind: SymKind) =
  if n.kind == DotToken:
    c.dest.add n
    inc n
  elif n.kind == ParLe and pool.tags[n.tagId] == "pragmas":
    c.dest.add n
    inc n
    while n.kind != ParRi:
      semPragma c, n, crucial, kind
    wantParRi c, n
  else:
    buildErr c, n.info, "expected '.' or 'pragmas'"

proc semSymUse(c: var SemContext; s: SymId): SymKind =
  result = NoSym

proc semIdentImpl(c: var SemContext; n: var Cursor; ident: StrId): SymKind =
  let insertPos = c.dest.len
  let info = n.info
  if buildSymChoice(c, ident, info, InnerMost) == 1:
    let sym = c.dest[insertPos+1].symId
    c.dest.shrink insertPos
    c.dest.add toToken(Symbol, sym, info)
    result = semSymUse(c, sym)
  else:
    result = NoSym

proc semIdent(c: var SemContext; n: var Cursor): SymKind =
  result = semIdentImpl(c, n, n.litId)
  inc n

proc semQuoted(c: var SemContext; n: var Cursor): SymKind =
  let nameId = unquote(n)
  result = semIdentImpl(c, n, nameId)

proc semTypeSym(c: var SemContext; kind: SymKind; info: PackedLineInfo) =
  if kind in {TypeY, TypevarY}:
    discard "fine"
  else:
    c.buildErr info, "type name expected, but got: " & $kind

proc semParams(c: var SemContext; n: var Cursor)

proc semObjectType(c: var SemContext; n: var Cursor) =
  # XXX implement me
  copyTree c, n

proc semEnumType(c: var SemContext; n: var Cursor) =
  # XXX implement me
  copyTree c, n

proc semConceptType(c: var SemContext; n: var Cursor) =
  # XXX implement me
  copyTree c, n

type
  TypeDeclContext = enum
    InLocalDecl, InTypeSection, InObjectDecl, InParamDecl, InInheritanceDecl, InReturnTypeDecl, AllowValues,
    InGenericConstraint

proc semLocalTypeImpl(c: var SemContext; n: var Cursor; context: TypeDeclContext) =
  let info = n.info
  case n.kind
  of Ident:
    let kind = semIdent(c, n)
    semTypeSym c, kind, info
  of Symbol:
    let kind = semSymUse(c, n.symId)
    inc n
    semTypeSym c, kind, info
  of ParLe:
    case typeKind(n)
    of NoType:
      if exprKind(n) == QuotedX:
        let kind = semQuoted(c, n)
        semTypeSym c, kind, info
      elif context == AllowValues:
        var it = Item(n: n, typ: c.types.autoType)
        semExpr c, it
        n = it.n
      else:
        c.buildErr info, "not a type"
    of IntT, FloatT, CharT, BoolT, UIntT, VoidT, StringT, NilT, AutoT, SymKindT:
      copyTree c, n
    of PtrT, RefT, MutT, OutT, LentT, SinkT, NotT, UncheckedArrayT, SetT, StaticT:
      takeToken c, n
      semLocalTypeImpl c, n, context
      wantParRi c, n
    of OrT, AndT:
      takeToken c, n
      semLocalTypeImpl c, n, context
      semLocalTypeImpl c, n, context
      wantParRi c, n
    of InvokeT:
      takeToken c, n
      semLocalTypeImpl c, n, context
      while n.kind != ParRi:
        semLocalTypeImpl c, n, AllowValues
      wantParRi c, n
    of TupleT:
      takeToken c, n
      while n.kind != ParRi:
        semLocalTypeImpl c, n, context
      wantParRi c, n
    of ArrayT:
      takeToken c, n
      semLocalTypeImpl c, n, AllowValues
      semLocalTypeImpl c, n, context
      wantParRi c, n
    of VarargsT:
      takeToken c, n
      semLocalTypeImpl c, n, context
      if n.kind == DotToken:
        takeToken c, n
        inc n
      else:
        var it = Item(n: n, typ: c.types.autoType)
        semExpr c, it
        # XXX Check the expression is a symchoice or a sym
        n = it.n
      wantParRi c, n
    of ObjectT:
      if context != InTypeSection:
        c.buildErr info, "`object` type must be defined in a `type` section"
        skip n
      else:
        semObjectType c, n
    of EnumT:
      if context != InTypeSection:
        c.buildErr info, "`enum` type must be defined in a `type` section"
        skip n
      else:
        semEnumType c, n
    of ConceptT:
      if context != InTypeSection:
        c.buildErr info, "`concept` type must be defined in a `type` section"
        skip n
      else:
        semConceptType c, n
    of DistinctT:
      if context != InTypeSection:
        c.buildErr info, "`distinct` type must be defined in a `type` section"
        skip n
      else:
        takeToken c, n
        semLocalTypeImpl c, n, context
        wantParRi c, n
    of ProcT, IterT:
      takeToken c, n
      wantDot c, n # name
      semParams c, n
      semLocalTypeImpl c, n, InReturnTypeDecl
      var ignored = default CrucialPragma
      semPragmas c, n, ignored, ProcY
      wantParRi c, n
  else:
    c.buildErr info, "not a type"

proc semLocalType(c: var SemContext; n: var Cursor): TypeCursor =
  let insertPos = c.dest.len
  semLocalTypeImpl c, n, InLocalDecl
  result = typeToCursor(c, insertPos)

proc semReturnType(c: var SemContext; n: var Cursor): TypeCursor =
  result = semLocalType(c, n)

proc exportMarkerBecomesNifTag(c: var SemContext; insertPos: int; crucial: CrucialPragma) =
  assert crucial.magic.len > 0
  let info = c.dest[insertPos].info
  c.dest[insertPos] = toToken(ParLe, pool.tags.getOrIncl(crucial.magic), info)
  if crucial.bits != 0:
    let arr = [toToken(IntLit, pool.integers.getOrIncl(crucial.bits), info),
               toToken(ParRi, 0'u32, info)]
    c.dest.insert arr, insertPos
  else:
    let arr = [toToken(ParRi, 0'u32, info)]
    c.dest.insert arr, insertPos

proc semLocal(c: var SemContext; n: var Cursor; kind: SymKind) =
  c.dest.add n
  inc n
  let delayed = handleSymDef(c, n, kind) # 0
  let beforeExportMarker = c.dest.len
  wantExportMarker c, n # 1
  var crucial = default CrucialPragma
  semPragmas c, n, crucial, kind # 2
  if crucial.magic.len > 0:
    exportMarkerBecomesNifTag c, beforeExportMarker, crucial
  case kind
  of TypevarY:
    discard semLocalType(c, n)
    wantDot c, n
  of ParamY, LetY, VarY, CursorY, ResultY:
    let beforeType = c.dest.len
    if n.kind == DotToken:
      # no explicit type given:
      inc n # 3
      var it = Item(n: n, typ: c.types.autoType)
      semExpr c, it # 4
      n = it.n
      patchType c, it.typ, beforeType
    else:
      let typ = semLocalType(c, n) # 3
      if n.kind == DotToken:
        # empty value
        takeToken c, n
      else:
        var it = Item(n: n, typ: typ)
        semExpr c, it # 4
        n = it.n
        patchType c, it.typ, beforeType
  else:
    assert false, "bug"
  c.addSym delayed
  wantParRi c, n

proc semLocal(c: var SemContext; it: var Item; kind: SymKind) =
  semLocal c, it.n, kind
  combineType it.typ, c.types.voidType

proc semGenericParam(c: var SemContext; n: var Cursor) =
  if n.kind == ParLe and pool.tags[n.tagId] == "typevar":
    semLocal c, n, TypevarY
  else:
    buildErr c, n.info, "expected 'typevar'"

proc semGenericParams(c: var SemContext; n: var Cursor) =
  if n.kind == DotToken:
    c.dest.add n
    inc n
  elif n.kind == ParLe and pool.tags[n.tagId] == "typevars":
    inc c.routine.inGeneric
    c.dest.add n
    inc n
    while n.kind != ParRi:
      semGenericParam c, n
    wantParRi c, n
  else:
    buildErr c, n.info, "expected '.' or 'typevars'"

proc semParam(c: var SemContext; n: var Cursor) =
  if n.kind == ParLe and pool.tags[n.tagId] == "param":
    semLocal c, n, ParamY
  else:
    buildErr c, n.info, "expected 'param'"

proc semParams(c: var SemContext; n: var Cursor) =
  if n.kind == DotToken:
    c.dest.add n
    inc n
  elif n.kind == ParLe and pool.tags[n.tagId] == "params":
    inc c.routine.inGeneric
    c.dest.add n
    inc n
    while n.kind != ParRi:
      semParam c, n
    wantParRi c, n
  else:
    buildErr c, n.info, "expected '.' or 'params'"

proc semProc(c: var SemContext; it: var Item; kind: SymKind) =
  declareOverloadableSym c, it, kind
  let beforeExportMarker = c.dest.len
  wantExportMarker c, it.n
  if it.n.kind == DotToken:
    c.dest.add it.n
    inc it.n
  else:
    buildErr c, it.n.info, "TR pattern not implemented"
    skip it.n
  c.routine = createSemRoutine(kind, c.routine)
  try:
    c.openScope() # open parameter scope
    semGenericParams c, it.n
    semParams c, it.n
    c.routine.returnType = semReturnType(c, it.n)
    if it.n.kind == DotToken:
      c.dest.add it.n
      inc it.n
    else:
      buildErr c, it.n.info, "`effects` must be empyt"
      skip it.n
    var crucial = default CrucialPragma
    semPragmas c, it.n, crucial, kind
    if crucial.magic.len > 0:
      exportMarkerBecomesNifTag c, beforeExportMarker, crucial
    c.openScope() # open body scope
    semProcBody c, it
    c.closeScope() # close body scope
    c.closeScope() # close parameter scope
  finally:
    c.routine = c.routine.parent

proc semStmts(c: var SemContext; it: var Item) =
  takeToken c, it.n
  while it.n.kind != ParRi:
    semStmt c, it.n
  wantParRi c, it.n
  combineType it.typ, c.types.voidType

proc semExpr(c: var SemContext; it: var Item) =
  case it.n.kind
  of IntLit:
    combineType it.typ, c.types.intType
    takeToken c, it.n
  of UIntLit:
    combineType it.typ, c.types.uintType
    takeToken c, it.n
  of FloatLit:
    combineType it.typ, c.types.floatType
    takeToken c, it.n
  of StringLit:
    combineType it.typ, c.types.stringType
    takeToken c, it.n
  of CharLit:
    combineType it.typ, c.types.charType
    takeToken c, it.n
  of Symbol, Ident:
    buildErr c, it.n.info, "not implemented"
  of ParLe:
    case exprKind(it.n)
    of NoExpr:
      case stmtKind(it.n)
      of NoStmt:
        buildErr c, it.n.info, "expression expected"
      of ProcS:
        semProc c, it, ProcY
      of FuncS:
        semProc c, it, FuncY
      of IterS:
        semProc c, it, IterY
      of ConverterS:
        semProc c, it, ConverterY
      of MethodS:
        semProc c, it, MethodY
      of MacroS:
        semProc c, it, MacroY
      of WhileS: semWhile c, it
      of VarS: semLocal c, it, VarY
      of LetS: semLocal c, it, LetY
      of CursorS: semLocal c, it, CursorY
      of ResultS: semLocal c, it, ResultY
      of ConstS: semLocal c, it, ConstY
      of StmtsS: semStmts c, it
      of BreakS: semBreak c, it
      of CallS: semCall c, it
      of EmitS, AsgnS, BlockS, IfS, ForS, CaseS, RetS, YieldS,
         TemplateS, TypeS:
        discard
    of FalseX, TrueX:
      combineType it.typ, c.types.boolType
      takeToken c, it.n
      wantParRi c, it.n
    of InfX, NegInfX, NanX:
      combineType it.typ, c.types.floatType
      takeToken c, it.n
      wantParRi c, it.n
    of AndX, OrX:
      takeToken c, it.n
      semBoolExpr c, it
      semBoolExpr c, it
      wantParRi c, it.n
    of NotX:
      c.dest.add it.n
      takeToken c, it.n
      semBoolExpr c, it
      wantParRi c, it.n
    of ParX:
      takeToken c, it.n
      semExpr c, it
      wantParRi c, it.n
    of CallX:
      semCall c, it
    of AconstrX, AtX, DerefX, DotX, PatX, AddrX, NilX, NegX, SizeofX, OconstrX, KvX,
       AddX, SubX, MulX, DivX, ModX, ShrX, ShlX, BitandX, BitorX, BitxorX, BitnotX,
       EqX, NeqX, LeX, LtX, CastX, ConvX, SufX, RangeX, RangesX,
       HderefX, HaddrX, OconvX, HconvX, OchoiceX, CchoiceX,
       TupleConstrX, SetX, QuotedX,
       CompilesX, DeclaredX, DefinedX, HighX, LowX, TypeofX, AshrX:
      takeToken c, it.n
      wantParRi c, it.n

  of ParRi, EofToken, SymbolDef, UnknownToken, DotToken:
    buildErr c, it.n.info, "expression expected"

proc reportErrors(c: var SemContext): int =
  let errTag = pool.tags.getOrIncl("err")
  var i = 0
  var r = Reporter(verbosity: 2)
  result = 0
  while i < c.dest.len:
    if c.dest[i].kind == ParLe and c.dest[i].tagId == errTag:
      inc result
      let info = c.dest[i].info
      inc i
      while c.dest[i].kind == UnknownToken:
        r.trace infoToStr(c.dest[i].info), "instantiation from here"
        inc i
      assert c.dest[i].kind == StringLit
      r.error infoToStr(info), pool.strings[c.dest[i].litId]
      inc i
    else:
      inc i

proc writeOutput(c: var SemContext; outfile: string) =
  #var b = nifbuilder.open(outfile)
  #b.addHeader "nimony", "nim-sem"
  #b.addRaw toString(c.dest)
  #b.close()
  writeFile outfile, "(.nif42)\n" & toString(c.dest)

proc semcheck*(infile, outfile: string) =
  var n = setupProgram(infile)
  var c = SemContext(
    dest: createTokenBuf(),
    types: createBuiltinTypes(),
    thisModuleSuffix: prog.main)
  c.currentScope = Scope(tab: initTable[StrId, seq[Sym]](), up: nil, kind: ToplevelScope)

  semStmt c, n
  if n.kind != EofToken:
    quit "Internal error: file not processed completely"
  # fix point: generic instantiations:
  when false:
    var i = 0
    while i < c.requires.len:
      let imp = c.requires[i]
      if not c.declared.contains(imp):
        importSymbol(c, imp)
      inc i
  if reportErrors(c) == 0:
    writeOutput c, outfile
