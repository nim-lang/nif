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

proc getIdent(e: var SemContext; c: var Cursor): StrId =
  var nested = 0
  while exprKind(c) in {OchoiceX, CchoiceX}:
    inc nested
    inc c
  case c.kind
  of Ident:
    result = c.litId
  of Symbol, SymbolDef:
    let sym = pool.syms[c.symId]
    var isGlobal = false
    result = pool.strings.getOrIncl(extractBasename(sym, isGlobal))
  of ParLe:
    if exprKind(c) == QuotedX:
      result = unquote(c)
    else:
      result = StrId(0)
  else:
    result = StrId(0)
  while nested > 0:
    if c.kind == ParRi: dec nested
    inc c

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

proc openScope(s: var SemContext) =
  s.currentScope = Scope(tab: initTable[StrId, seq[Sym]](), up: s.currentScope, kind: NormalScope)

proc closeScope(s: var SemContext) =
  s.currentScope = s.currentScope.up

# -------------------------- error handling -------------------------

proc pushErrorContext(c: var SemContext; info: PackedLineInfo) = c.instantiatedFrom.add info
proc popErrorContext(c: var SemContext) = discard c.instantiatedFrom.pop

proc buildErr*(c: var SemContext; info: PackedLineInfo; msg: string) =
  c.dest.buildTree ErrT, info:
    for instFrom in items(c.instantiatedFrom):
      c.dest.add toToken(UnknownToken, 0'u32, instFrom)
    c.dest.add toToken(StringLit, pool.strings.getOrIncl(msg), info)

# -------------------------- type handling ---------------------------

proc typeToCanon(e: var SemContext; start: int): string =
  result = ""
  for i in start..<e.dest.len:
    case e.dest[i].kind
    of ParLe:
      result.add '('
      result.addInt e.dest[i].tagId.int
    of ParRi: result.add ')'
    of Ident, StringLit:
      result.add ' '
      result.addInt e.dest[i].litId.int
    of UnknownToken: result.add " unknown"
    of EofToken: result.add " eof"
    of DotToken: result.add '.'
    of Symbol, SymbolDef:
      result.add " s"
      result.addInt e.dest[i].symId.int
    of CharLit:
      result.add " c"
      result.addInt e.dest[i].uoperand.int
    of IntLit:
      result.add " i"
      result.addInt e.dest[i].intId.int
    of UIntLit:
      result.add " u"
      result.addInt e.dest[i].uintId.int
    of FloatLit:
      result.add " f"
      result.addInt e.dest[i].floatId.int

proc typeToCursor(e: var SemContext; start: int): TypeCursor =
  let key = typeToCanon(e, start)
  if e.typeMem.hasKey(key):
    result = cursorAt(e.typeMem[key], 0)
  else:
    var buf = createTokenBuf(e.dest.len - start)
    for i in start..<e.dest.len:
      buf.add e.dest[i]
    result = cursorAt(buf, 0)
    e.typeMem[key] = buf

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

proc declareOverloadableSym(c: var SemContext; it: var Item; kind: SymKind) =
  let info = it.n.info
  if it.n.kind == Ident:
    let lit = it.n.litId
    let s = Sym(name: identToSym(c, lit),
                kind: kind, pos: 0'i32)
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
      let s = Sym(name: identToSym(c, lit),
                  kind: kind, pos: 0'i32)
      addOverloadable(c.currentScope, lit, s)
      c.dest.add toToken(SymbolDef, s.name, info)
      inc it.n

proc success(s: SymStatus): bool {.inline.} = s in {OkNew, OkExisting}
proc success(s: DelayedSym): bool {.inline.} = success s.status

proc handleSymDef(e: var SemContext; c: var Cursor; kind: SymKind): DelayedSym =
  let info = c.info
  if c.kind == Ident:
    let lit = c.litId
    let def = identToSym(e, lit)
    let s = Sym(name: def,
                kind: kind, pos: 0'i32)
    result = DelayedSym(status: OkNew, lit: lit, s: s, info: info)
    e.dest.add toToken(SymbolDef, def, info)
    inc c
  elif c.kind == SymbolDef:
    discard "ok, and no need to re-add it to the symbol table"
    result = DelayedSym(status: OkExisting, info: info)
    e.dest.add c
    inc c
  else:
    let lit = getIdent(e, c)
    if lit == StrId(0):
      e.buildErr info, "identifier expected"
      result = DelayedSym(status: ErrNoIdent, info: info)
    else:
      let def = identToSym(e, lit)
      let s = Sym(name: def,
                  kind: kind, pos: 0'i32)
      result = DelayedSym(status: OkNew, lit: lit, s: s, info: info)
      e.dest.add toToken(SymbolDef, def, info)

proc addSym(c: var SemContext; s: DelayedSym) =
  if s.status == OkNew:
    if addNonOverloadable(c.currentScope, s.lit, s.s) == Conflict:
      c.buildErr s.info, "attempt to redeclare: " & pool.strings[s.lit]

# -------------------------------------------------------------------------------------------------

proc copyTree(e: var SemContext; c: var Cursor) =
  var nested = 0
  if c.kind != ParLe:
    e.dest.add c
  else:
    while true:
      e.dest.add c
      case c.kind
      of Parle: inc nested
      of ParRi:
        e.dest.add c
        if nested == 0:
          inc c
          break
        dec nested
      of EofToken:
        error "expected ')', but EOF reached"
        break
      else: discard
      inc c

# -------------------------------------------------------------

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

proc wantDot(e: var SemContext; c: var Cursor) =
  if c.kind == DotToken:
    e.dest.add c
    inc c
  else:
    buildErr e, c.info, "expected '.'"

proc semExpr(e: var SemContext; it: var Item)

proc classifyType(e: var SemContext; c: Cursor): TypeKind =
  result = typeKind(c)

proc semBoolExpr(e: var SemContext; it: var Item) =
  semExpr e, it
  if classifyType(e, it.typ) != BoolT:
    buildErr e, it.n.info, "expected `bool` but got: " & typeToString(e, it.typ)

proc semProcBody(e: var SemContext; itB: var Item) =
  #let beforeBodyPos = e.dest.len
  var it = Item(n: itB.n, typ: e.types.autoType)
  semExpr e, it
  if classifyType(e, it.typ) == VoidT:
    discard "ok"
  else:
    # XXX
    buildErr e, itB.n.info, "proc body as expression not implemented"
  itB.n = it.n

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

proc combineType(dest: var Cursor; src: Cursor) =
  if typeKind(dest) == AutoT:
    dest = src

proc semWhile(e: var SemContext; it: var Item) =
  e.dest.add it.n
  inc it.n
  semBoolExpr e, it
  inc e.routine.inLoop
  semStmt e, it.n
  dec e.routine.inLoop
  wantParRi e, it.n
  combineType it.typ, e.types.voidType

proc semBreak(e: var SemContext; it: var Item) =
  takeToken e, it.n
  if e.routine.inLoop+e.routine.inBlock == 0:
    buildErr e, it.n.info, "`break` only possible within a `while` or `block` statement"
  else:
    wantDot e, it.n
  wantParRi e, it.n
  combineType it.typ, e.types.voidType

proc wantExportMarker(e: var SemContext; c: var Cursor) =
  if c.kind == DotToken:
    e.dest.add c
    inc c
  elif c.kind == Ident and pool.strings[c.litId] == "x":
    if e.currentScope.kind != ToplevelScope:
      buildErr e, c.info, "only toplevel declarations can be exported"
    else:
      e.dest.add c
    inc c
  elif c.kind == ParLe:
    # export marker could have been turned into a NIF tag
    copyTree e, c
  else:
    buildErr e, c.info, "expected '.' or 'x' for an export marker"

proc patchType(e: var SemContext; typ: TypeCursor; patchPosition: int) =
  discard "XXX to implement"

type
  CrucialPragma* = object
    magic: string
    bits: int

proc semPragma(e: var SemContext; c: var Cursor; crucial: var CrucialPragma; kind: SymKind) =
  case pragmaKind(c)
  of NoPragma:
    if kind.isRoutine and callConvKind(c) != NoCallConv:
      takeToken e, c
      wantParRi e, c
    else:
      buildErr e, c.info, "expected pragma"
  of Magic:
    takeToken e, c
    if c.kind in {StringLit, Ident}:
      let m = parseMagic(pool.strings[c.litId])
      if m == mNone:
        buildErr e, c.info, "unknown `magic`"
      else:
        let (magicWord, bits) = magicToTag(m)
        crucial.magic = magicWord
        crucial.bits = bits
      takeToken e, c
    else:
      buildErr e, c.info, "`magic` pragma takes a string literal"
    wantParRi e, c
  of ImportC, ImportCpp, ExportC, Nodecl, Header, Align, Bits, Selectany,
     Threadvar, Globalvar:
    copyTree e, c

proc semPragmas(e: var SemContext; c: var Cursor; crucial: var CrucialPragma; kind: SymKind) =
  if c.kind == DotToken:
    e.dest.add c
    inc c
  elif c.kind == ParLe and pool.tags[c.tagId] == "pragmas":
    e.dest.add c
    inc c
    while c.kind != ParRi:
      semPragma e, c, crucial, kind
    wantParRi e, c
  else:
    buildErr e, c.info, "expected '.' or 'pragmas'"

proc semSymUse(e: var SemContext; s: SymId): SymKind =
  result = NoSym

proc semIdentImpl(e: var SemContext; c: var Cursor; ident: StrId): SymKind =
  let insertPos = e.dest.len
  let info = c.info
  if buildSymChoice(e, ident, info, InnerMost) == 1:
    let sym = e.dest[insertPos+1].symId
    e.dest.shrink insertPos
    e.dest.add toToken(Symbol, sym, info)
    result = semSymUse(e, sym)
  else:
    result = NoSym

proc semIdent(e: var SemContext; c: var Cursor): SymKind =
  result = semIdentImpl(e, c, c.litId)
  inc c

proc semQuoted(e: var SemContext; c: var Cursor): SymKind =
  let nameId = unquote(c)
  result = semIdentImpl(e, c, nameId)

proc semTypeSym(e: var SemContext; kind: SymKind; info: PackedLineInfo) =
  if kind in {TypeY, TypevarY}:
    discard "fine"
  else:
    e.buildErr info, "type name expected, but got: " & $kind

proc semParams(e: var SemContext; c: var Cursor)

proc semObjectType(e: var SemContext; c: var Cursor) =
  # XXX implement me
  copyTree e, c

proc semEnumType(e: var SemContext; c: var Cursor) =
  # XXX implement me
  copyTree e, c

proc semConceptType(e: var SemContext; c: var Cursor) =
  # XXX implement me
  copyTree e, c

type
  TypeDeclContext = enum
    InLocalDecl, InTypeSection, InObjectDecl, InParamDecl, InInheritanceDecl, InReturnTypeDecl, AllowValues,
    InGenericConstraint

proc semLocalTypeImpl(e: var SemContext; c: var Cursor; context: TypeDeclContext) =
  let info = c.info
  case c.kind
  of Ident:
    let kind = semIdent(e, c)
    semTypeSym e, kind, info
  of Symbol:
    let kind = semSymUse(e, c.symId)
    inc c
    semTypeSym e, kind, info
  of ParLe:
    case typeKind(c)
    of NoType:
      if exprKind(c) == QuotedX:
        let kind = semQuoted(e, c)
        semTypeSym e, kind, info
      elif context == AllowValues:
        var it = Item(n: c, typ: e.types.autoType)
        semExpr e, it
        c = it.n
      else:
        e.buildErr info, "not a type"
    of IntT, FloatT, CharT, BoolT, UIntT, VoidT, StringT, NilT, AutoT, SymKindT:
      copyTree e, c
    of PtrT, RefT, MutT, OutT, LentT, SinkT, NotT, UncheckedArrayT, SetT, StaticT:
      takeToken e, c
      semLocalTypeImpl e, c, context
      wantParRi e, c
    of OrT, AndT:
      takeToken e, c
      semLocalTypeImpl e, c, context
      semLocalTypeImpl e, c, context
      wantParRi e, c
    of InvokeT:
      takeToken e, c
      semLocalTypeImpl e, c, context
      while c.kind != ParRi:
        semLocalTypeImpl e, c, AllowValues
      wantParRi e, c
    of TupleT:
      takeToken e, c
      while c.kind != ParRi:
        semLocalTypeImpl e, c, context
      wantParRi e, c
    of ArrayT:
      takeToken e, c
      semLocalTypeImpl e, c, AllowValues
      semLocalTypeImpl e, c, context
      wantParRi e, c
    of VarargsT:
      takeToken e, c
      semLocalTypeImpl e, c, context
      if c.kind == DotToken:
        takeToken e, c
        inc c
      else:
        var it = Item(n: c, typ: e.types.autoType)
        semExpr e, it
        # XXX Check the expression is a symchoice or a sym
        c = it.n
      wantParRi e, c
    of ObjectT:
      if context != InTypeSection:
        e.buildErr info, "`object` type must be defined in a `type` section"
        skip c
      else:
        semObjectType e, c
    of EnumT:
      if context != InTypeSection:
        e.buildErr info, "`enum` type must be defined in a `type` section"
        skip c
      else:
        semEnumType e, c
    of ConceptT:
      if context != InTypeSection:
        e.buildErr info, "`concept` type must be defined in a `type` section"
        skip c
      else:
        semConceptType e, c
    of DistinctT:
      if context != InTypeSection:
        e.buildErr info, "`distinct` type must be defined in a `type` section"
        skip c
      else:
        takeToken e, c
        semLocalTypeImpl e, c, context
        wantParRi e, c
    of ProcT, IterT:
      takeToken e, c
      wantDot e, c # name
      semParams e, c
      semLocalTypeImpl e, c, InReturnTypeDecl
      var ignored = default CrucialPragma
      semPragmas e, c, ignored, ProcY
      wantParRi e, c
  else:
    e.buildErr info, "not a type"

proc semLocalType(e: var SemContext; c: var Cursor): TypeCursor =
  let insertPos = e.dest.len
  semLocalTypeImpl e, c, InLocalDecl
  result = typeToCursor(e, insertPos)

proc semReturnType(e: var SemContext; c: var Cursor): TypeCursor =
  result = semLocalType(e, c)

proc exportMarkerBecomesNifTag(e: var SemContext; insertPos: int; crucial: CrucialPragma) =
  assert crucial.magic.len > 0
  let info = e.dest[insertPos].info
  e.dest[insertPos] = toToken(ParLe, pool.tags.getOrIncl(crucial.magic), info)
  if crucial.bits != 0:
    let arr = [toToken(IntLit, pool.integers.getOrIncl(crucial.bits), info),
               toToken(ParRi, 0'u32, info)]
    e.dest.insert arr, insertPos
  else:
    let arr = [toToken(ParRi, 0'u32, info)]
    e.dest.insert arr, insertPos

proc semLocal(e: var SemContext; c: var Cursor; kind: SymKind) =
  e.dest.add c
  inc c
  let delayed = handleSymDef(e, c, kind) # 0
  let beforeExportMarker = e.dest.len
  wantExportMarker e, c # 1
  var crucial = default CrucialPragma
  semPragmas e, c, crucial, kind # 2
  if crucial.magic.len > 0:
    exportMarkerBecomesNifTag e, beforeExportMarker, crucial
  case kind
  of TypevarY:
    discard semLocalType(e, c)
    wantDot e, c
  of ParamY, LetY, VarY, CursorY, ResultY:
    let beforeType = e.dest.len
    if c.kind == DotToken:
      # no explicit type given:
      inc c # 3
      var it = Item(n: c, typ: e.types.autoType)
      semExpr e, it # 4
      c = it.n
      patchType e, it.typ, beforeType
    else:
      let typ = semLocalType(e, c) # 3
      if c.kind == DotToken:
        # empty value
        takeToken e, c
      else:
        var it = Item(n: c, typ: typ)
        semExpr e, it # 4
        c = it.n
        patchType e, it.typ, beforeType
  else:
    assert false, "bug"
  e.addSym delayed
  wantParRi e, c

proc semLocal(e: var SemContext; it: var Item; kind: SymKind) =
  semLocal e, it.n, kind
  combineType it.typ, e.types.voidType

proc semGenericParam(e: var SemContext; c: var Cursor) =
  if c.kind == ParLe and pool.tags[c.tagId] == "typevar":
    semLocal e, c, TypevarY
  else:
    buildErr e, c.info, "expected 'typevar'"

proc semGenericParams(e: var SemContext; c: var Cursor) =
  if c.kind == DotToken:
    e.dest.add c
    inc c
  elif c.kind == ParLe and pool.tags[c.tagId] == "typevars":
    inc e.routine.inGeneric
    e.dest.add c
    inc c
    while c.kind != ParRi:
      semGenericParam e, c
    wantParRi e, c
  else:
    buildErr e, c.info, "expected '.' or 'typevars'"

proc semParam(e: var SemContext; c: var Cursor) =
  if c.kind == ParLe and pool.tags[c.tagId] == "param":
    semLocal e, c, ParamY
  else:
    buildErr e, c.info, "expected 'param'"

proc semParams(e: var SemContext; c: var Cursor) =
  if c.kind == DotToken:
    e.dest.add c
    inc c
  elif c.kind == ParLe and pool.tags[c.tagId] == "params":
    inc e.routine.inGeneric
    e.dest.add c
    inc c
    while c.kind != ParRi:
      semParam e, c
    wantParRi e, c
  else:
    buildErr e, c.info, "expected '.' or 'params'"

proc semProc(e: var SemContext; it: var Item; kind: SymKind) =
  declareOverloadableSym e, it, kind
  let beforeExportMarker = e.dest.len
  wantExportMarker e, it.n
  if it.n.kind == DotToken:
    e.dest.add it.n
    inc it.n
  else:
    buildErr e, it.n.info, "TR pattern not implemented"
    skip it.n
  e.routine = createSemRoutine(kind, e.routine)
  try:
    e.openScope() # open parameter scope
    semGenericParams e, it.n
    semParams e, it.n
    e.routine.returnType = semReturnType(e, it.n)
    if it.n.kind == DotToken:
      e.dest.add it.n
      inc it.n
    else:
      buildErr e, it.n.info, "`effects` must be empyt"
      skip it.n
    var crucial = default CrucialPragma
    semPragmas e, it.n, crucial, kind
    if crucial.magic.len > 0:
      exportMarkerBecomesNifTag e, beforeExportMarker, crucial
    e.openScope() # open body scope
    semProcBody e, it
    e.closeScope() # close body scope
    e.closeScope() # close parameter scope
  finally:
    e.routine = e.routine.parent

proc semStmts(e: var SemContext; it: var Item) =
  takeToken e, it.n
  while it.n.kind != ParRi:
    semStmt e, it.n
  wantParRi e, it.n
  combineType it.typ, e.types.voidType

proc semExpr(e: var SemContext; it: var Item) =
  case it.n.kind
  of IntLit:
    combineType it.typ, e.types.intType
    takeToken e, it.n
  of UIntLit:
    combineType it.typ, e.types.uintType
    takeToken e, it.n
  of FloatLit:
    combineType it.typ, e.types.floatType
    takeToken e, it.n
  of StringLit:
    combineType it.typ, e.types.stringType
    takeToken e, it.n
  of CharLit:
    combineType it.typ, e.types.charType
    takeToken e, it.n
  of Symbol, Ident:
    buildErr e, it.n.info, "not implemented"
  of ParLe:
    case exprKind(it.n)
    of NoExpr:
      case stmtKind(it.n)
      of NoStmt:
        buildErr e, it.n.info, "expression expected"
      of ProcS:
        semProc e, it, ProcY
      of FuncS:
        semProc e, it, FuncY
      of IterS:
        semProc e, it, IterY
      of ConverterS:
        semProc e, it, ConverterY
      of MethodS:
        semProc e, it, MethodY
      of MacroS:
        semProc e, it, MacroY
      of WhileS: semWhile e, it
      of VarS: semLocal e, it, VarY
      of LetS: semLocal e, it, LetY
      of CursorS: semLocal e, it, CursorY
      of ResultS: semLocal e, it, ResultY
      of ConstS: semLocal e, it, ConstY
      of StmtsS: semStmts e, it
      of BreakS: semBreak e, it
      of CallS: semCall e, it
      of EmitS, AsgnS, BlockS, IfS, ForS, CaseS, RetS, YieldS,
         TemplateS, TypeS:
        discard
    of FalseX, TrueX:
      combineType it.typ, e.types.boolType
      takeToken e, it.n
      wantParRi e, it.n
    of InfX, NegInfX, NanX:
      combineType it.typ, e.types.floatType
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
       HderefX, HaddrX, OconvX, HconvX, OchoiceX, CchoiceX,
       TupleConstrX, SetX, QuotedX,
       CompilesX, DeclaredX, DefinedX, HighX, LowX, TypeofX, AshrX:
      takeToken e, it.n
      wantParRi e, it.n

  of ParRi, EofToken, SymbolDef, UnknownToken, DotToken:
    buildErr e, it.n.info, "expression expected"

proc reportErrors(e: var SemContext): int =
  let errTag = pool.tags.getOrIncl("err")
  var i = 0
  var r = Reporter(verbosity: 2)
  result = 0
  while i < e.dest.len:
    if e.dest[i].kind == ParLe and e.dest[i].tagId == errTag:
      inc result
      let info = e.dest[i].info
      inc i
      while e.dest[i].kind == UnknownToken:
        r.trace infoToStr(e.dest[i].info), "instantiation from here"
        inc i
      assert e.dest[i].kind == StringLit
      r.error infoToStr(info), pool.strings[e.dest[i].litId]
      inc i
    else:
      inc i

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
  if reportErrors(e) == 0:
    writeOutput e, outfile
