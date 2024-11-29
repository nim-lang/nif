#       Nimony
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Semantic checking:
## Most important task is to turn identifiers into symbols and to perform
## type checking.

import std / [tables, sets, os, syncio, formatfloat, assertions]
include nifprelude
import nimony_model, symtabs, builtintypes, decls, symparser,
  programs, sigmatch, magics, reporters, nifconfig, nifindexes

import ".." / gear2 / modnames

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
  ImportedModule = object
    iface: Iface

  InstRequest* = object
    origin*: SymId
    targetSym*: SymId
    targetType*: TypeCursor
    #typeParams*: seq[TypeCursor]
    inferred*: Table[SymId, Cursor]
    requestFrom*: seq[PackedLineInfo]

  ProgramContext = ref object # shared for every `SemContext`
    config: NifConfig

  ObjField = object
    sym: SymId
    level: int # inheritance level
    typ: TypeCursor

  SemContext = object
    dest: TokenBuf
    routine: SemRoutine
    currentScope: Scope
    g: ProgramContext
    typeRequests, procRequests: seq[InstRequest]
    includeStack: seq[string]
    #importedModules: seq[ImportedModule]
    instantiatedFrom: seq[PackedLineInfo]
    importTab: Iface
    globals, locals: Table[string, int]
    types: BuiltinTypes
    typeMem: Table[string, TokenBuf]
    thisModuleSuffix: string
    processedModules: HashSet[string]
    #fieldsCache: Table[SymId, Table[StrId, ObjField]]

# -------------- symbol lookups -------------------------------------

proc unquote(c: var Cursor): StrId =
  var r = ""
  while true:
    case c.kind
    of ParLe:
      inc c
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
    of UnknownToken, DotToken, Symbol, SymbolDef:
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
    inc n
  of Symbol, SymbolDef:
    let sym = pool.syms[n.symId]
    var isGlobal = false
    result = pool.strings.getOrIncl(extractBasename(sym, isGlobal))
    inc n
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

template buildTree*(dest: var TokenBuf; kind: StmtKind|ExprKind|TypeKind|SymKind;
                    info: PackedLineInfo; body: untyped) =
  dest.add toToken(ParLe, pool.tags.getOrIncl($kind), info)
  body
  dest.addParRi()

proc considerImportedSymbols(c: var SemContext; name: StrId; info: PackedLineInfo): int =
  result = 0
  let candidates = c.importTab.getOrDefault(name)
  inc result, candidates.len
  for defId in candidates:
    c.dest.add toToken(Symbol, defId, info)

proc addSymUse(dest: var TokenBuf; s: Sym; info: PackedLineInfo) =
  dest.add toToken(Symbol, s.name, info)

proc addSymUse(dest: var TokenBuf; s: SymId; info: PackedLineInfo) =
  dest.add toToken(Symbol, s, info)

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

template withNewScope(c: var SemContext; body: untyped) =
  openScope(c)
  try:
    body
  finally:
    closeScope(c)

# -------------------------- error handling -------------------------

proc pushErrorContext(c: var SemContext; info: PackedLineInfo) = c.instantiatedFrom.add info
proc popErrorContext(c: var SemContext) = discard c.instantiatedFrom.pop

template withErrorContext(c: var SemContext; info: PackedLineInfo; body: untyped) =
  pushErrorContext(c, info)
  try:
    body
  finally:
    popErrorContext(c)

proc buildErr*(c: var SemContext; info: PackedLineInfo; msg: string) =
  when defined(debug):
    writeStackTrace()
    echo infoToStr(info) & " Error: " & msg
    quit msg
  c.dest.buildTree ErrT, info:
    for instFrom in items(c.instantiatedFrom):
      c.dest.add toToken(UnknownToken, 0'u32, instFrom)
    c.dest.add toToken(StringLit, pool.strings.getOrIncl(msg), info)

# -------------------------- type handling ---------------------------

proc typeToCanon(buf: TokenBuf; start: int): string =
  result = ""
  for i in start..<buf.len:
    case buf[i].kind
    of ParLe:
      result.add '('
      result.addInt buf[i].tagId.int
    of ParRi: result.add ')'
    of Ident, StringLit:
      result.add ' '
      result.addInt buf[i].litId.int
    of UnknownToken: result.add " unknown"
    of EofToken: result.add " eof"
    of DotToken: result.add '.'
    of Symbol, SymbolDef:
      result.add " s"
      result.addInt buf[i].symId.int
    of CharLit:
      result.add " c"
      result.addInt buf[i].uoperand.int
    of IntLit:
      result.add " i"
      result.addInt buf[i].intId.int
    of UIntLit:
      result.add " u"
      result.addInt buf[i].uintId.int
    of FloatLit:
      result.add " f"
      result.addInt buf[i].floatId.int

proc sameTrees(a, b: TypeCursor): bool =
  var a = a
  var b = b
  var nested = 0
  while true:
    if a.kind != b.kind: return false
    case a.kind
    of ParLe:
      if a.tagId != b.tagId: return false
      inc nested
    of ParRi:
      dec nested
      if nested == 0: return true
    of Symbol, SymbolDef:
      if a.symId != b.symId: return false
    of IntLit:
      if a.intId != b.intId: return false
    of UIntLit:
      if a.uintId != b.uintId: return false
    of FloatLit:
      if a.floatId != b.floatId: return false
    of StringLit, Ident:
      if a.litId != b.litId: return false
    of CharLit, UnknownToken:
      if a.uoperand != b.uoperand: return false
    of DotToken, EofToken: discard "nothing else to compare"
    inc a
    inc b

proc typeToCursor(c: var SemContext; buf: TokenBuf; start: int): TypeCursor =
  let key = typeToCanon(buf, start)
  if c.typeMem.hasKey(key):
    result = cursorAt(c.typeMem[key], 0)
  else:
    var newBuf = createTokenBuf(buf.len - start)
    for i in start..<buf.len:
      newBuf.add buf[i]
    result = cursorAt(newBuf, 0)
    c.typeMem[key] = newBuf

proc typeToCursor(c: var SemContext; start: int): TypeCursor =
  typeToCursor(c, c.dest, start)

proc declToCursor(c: var SemContext; s: Sym): LoadResult =
  if knowsSym(s.name) or s.pos == ImportedPos:
    result = tryLoadSym(s.name)
  elif s.pos > 0:
    var buf = createTokenBuf(10)
    var pos = s.pos - 1
    var nested = 0
    # XXX optimize this for non-generic procs. No need to
    # copy their bodies here.
    while true:
      buf.add c.dest[pos]
      case c.dest[pos].kind
      of ParLe: inc nested
      of ParRi:
        dec nested
        if nested == 0: break
      else: discard
      inc pos
    result = LoadResult(status: LacksNothing, decl: cursorAt(buf, 0))
    publish s.name, buf
  else:
    result = LoadResult(status: LacksPosition)

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

proc identToSym(c: var SemContext; lit: StrId; kind: SymKind): SymId =
  var name = pool.strings[lit]
  if c.currentScope.kind == ToplevelScope or kind in {FldY, EfldY}:
    c.makeGlobalSym(name)
  else:
    c.makeLocalSym(name)
  result = pool.syms.getOrIncl(name)

proc declareSym(c: var SemContext; it: var Item; kind: SymKind): SymStatus =
  let info = it.n.info
  if it.n.kind == Ident:
    let lit = it.n.litId
    let s = Sym(kind: kind, name: identToSym(c, lit, kind),
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

proc declareOverloadableSym(c: var SemContext; it: var Item; kind: SymKind): SymId =
  let info = it.n.info
  if it.n.kind == Ident:
    let lit = it.n.litId
    result = identToSym(c, lit, kind)
    let s = Sym(kind: kind, name: result,
                pos: c.dest.len)
    addOverloadable(c.currentScope, lit, s)
    c.dest.add toToken(SymbolDef, s.name, info)
    inc it.n
  elif it.n.kind == SymbolDef:
    result = it.n.symId
    c.dest.add it.n
    inc it.n
  else:
    let lit = getIdent(c, it.n)
    if lit == StrId(0):
      c.buildErr info, "identifier expected"
      result = SymId(0)
    else:
      result = identToSym(c, lit, kind)
      let s = Sym(kind: kind, name: result,
                  pos: c.dest.len)
      addOverloadable(c.currentScope, lit, s)
      c.dest.add toToken(SymbolDef, s.name, info)

proc success(s: SymStatus): bool {.inline.} = s in {OkNew, OkExisting}
proc success(s: DelayedSym): bool {.inline.} = success s.status

proc handleSymDef(c: var SemContext; n: var Cursor; kind: SymKind): DelayedSym =
  let info = n.info
  if n.kind == Ident:
    let lit = n.litId
    let def = identToSym(c, lit, kind)
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
      let def = identToSym(c, lit, kind)
      let s = Sym(kind: kind, name: def,
                  pos: c.dest.len)
      result = DelayedSym(status: OkNew, lit: lit, s: s, info: info)
      c.dest.add toToken(SymbolDef, def, info)

proc addSym(c: var SemContext; s: DelayedSym) =
  if s.status == OkNew:
    if addNonOverloadable(c.currentScope, s.lit, s.s) == Conflict:
      c.buildErr s.info, "attempt to redeclare: " & pool.strings[s.lit]

proc publish(c: var SemContext; s: SymId; start: int) =
  var buf = createTokenBuf(c.dest.len - start + 1)
  for i in start..<c.dest.len:
    buf.add c.dest[i]
  programs.publish s, buf

proc publishSignature(c: var SemContext; s: SymId; start: int) =
  var buf = createTokenBuf(c.dest.len - start + 3)
  for i in start..<c.dest.len:
    buf.add c.dest[i]
  buf.addDotToken() # body is empty for a signature
  buf.addParRi()
  programs.publish s, buf

# -------------------------------------------------------------------------------------------------

proc takeTree(dest: var TokenBuf; n: var Cursor) =
  if n.kind != ParLe:
    dest.add n
  else:
    var nested = 0
    while true:
      dest.add n
      case n.kind
      of ParLe: inc nested
      of ParRi:
        dec nested
        if nested == 0:
          inc n
          break
      of EofToken:
        error "expected ')', but EOF reached"
        break
      else: discard
      inc n

proc takeTree(c: var SemContext; n: var Cursor) =
  takeTree c.dest, n

proc copyTree(dest: var TokenBuf; n: Cursor) =
  var n = n
  takeTree dest, n

# -------------------------------------------------------------

proc wantParRi(c: var SemContext; n: var Cursor) =
  if n.kind == ParRi:
    c.dest.add n
    inc n
  else:
    error "expected ')', but got: ", n

proc skipParRi(n: var Cursor) =
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

# -------------------- path handling ----------------------------

proc stdFile(f: string): string =
  getAppDir() / "lib" / f

proc resolveFile*(c: SemContext; origin: string; toResolve: string): string =
  let nimFile = toResolve.addFileExt(".nim")
  #if toResolve.startsWith("std/") or toResolve.startsWith("ext/"):
  #  result = stdFile nimFile
  if toResolve.isAbsolute:
    result = nimFile
  else:
    result = splitFile(origin).dir / nimFile
    var i = 0
    while not fileExists(result) and i < c.g.config.paths.len:
      result = c.g.config.paths[i] / nimFile
      inc i

proc filenameVal(n: var Cursor; res: var seq[string]; hasError: var bool) =
  case n.kind
  of StringLit, Ident:
    res.add pool.strings[n.litId]
    inc n
  of Symbol:
    var s = pool.syms[n.symId]
    extractBasename s
    res.add s
    inc n
  of ParLe:
    case exprKind(n)
    of OchoiceX, CchoiceX:
      inc n
      if n.kind != ParRi:
        filenameVal(n, res, hasError)
        while n.kind != ParRi: skip n
        inc n
      else:
        hasError = true
        inc n
    of CallX, InfixX:
      var x = n
      skip n # ensure we skipped it completely
      inc x
      var isSlash = false
      case x.kind
      of StringLit, Ident:
        isSlash = pool.strings[x.litId] == "/"
      of Symbol:
        var s = pool.syms[x.symId]
        extractBasename s
        isSlash = s == "/"
      else: hasError = true
      if not hasError:
        inc x # skip slash
        var prefix: seq[string] = @[]
        filenameVal(x, prefix, hasError)
        var suffix: seq[string] = @[]
        filenameVal(x, suffix, hasError)
        if x.kind != ParRi: hasError = true
        for pre in mitems(prefix):
          for suf in mitems(suffix):
            if pre != "" and suf != "":
              res.add pre & "/" & suf
            else:
              hasError = true
        if prefix.len == 0 or suffix.len == 0:
          hasError = true
      else:
        hasError = true
    of ParX, AconstrX:
      inc n
      if n.kind != ParRi:
        while n.kind != ParRi:
          filenameVal(n, res, hasError)
        inc n
      else:
        hasError = true
        inc n
    of TupleConstrX:
      inc n
      skip n # skip type
      if n.kind != ParRi:
        while n.kind != ParRi:
          filenameVal(n, res, hasError)
        inc n
      else:
        hasError = true
        inc n
    else:
      skip n
      hasError = true
  else:
    skip n
    hasError = true

# ------------------ include/import handling ------------------------

proc findTool*(name: string): string =
  let exe = name.addFileExt(ExeExt)
  result = getAppDir() / exe

proc exec*(cmd: string) =
  if execShellCmd(cmd) != 0: quit("FAILURE: " & cmd)

proc parseFile(nimFile: string; paths: openArray[string]): TokenBuf =
  let nifler = findTool("nifler")
  let name = moduleSuffix(nimFile, paths)
  let src = "nifcache" / name & ".1.nif"
  exec quoteShell(nifler) & " --portablePaths p " & quoteShell(nimFile) & " " &
    quoteShell(src)

  var stream = nifstreams.open(src)
  try:
    discard processDirectives(stream.r)
    result = fromStream(stream)
  finally:
    nifstreams.close(stream)

proc semStmt(c: var SemContext; n: var Cursor)

proc typeMismatch(c: var SemContext; info: PackedLineInfo; got, expected: TypeCursor) =
  c.buildErr info, "type mismatch: got: " & typeToString(got) & " but wanted: " & typeToString(expected)

proc combineType(c: var SemContext; info: PackedLineInfo; dest: var Cursor; src: Cursor) =
  if typeKind(dest) == AutoT:
    dest = src
  elif sameTrees(dest, src):
    discard "fine"
  else:
    c.typeMismatch info, src, dest

proc producesVoid(c: var SemContext; info: PackedLineInfo; dest: var Cursor) =
  if typeKind(dest) in {AutoT, VoidT}:
    combineType c, info, dest, c.types.voidType
  else:
    c.typeMismatch info, c.types.voidType, dest

proc getFile(c: var SemContext; info: PackedLineInfo): string =
  let (fid, _, _) = unpack(pool.man, info)
  result = pool.files[fid]

proc semInclude(c: var SemContext; it: var Item) =
  var files: seq[string] = @[]
  var hasError = false
  let info = it.n.info
  var x = it.n
  takeTree c, it.n
  inc x # skip the `include`
  filenameVal(x, files, hasError)

  if hasError:
    c.buildErr info, "wrong `include` statement"
  else:
    for f1 in items(files):
      let f2 = resolveFile(c, getFile(c, info), f1)
      # check for recursive include files:
      var isRecursive = false
      for a in c.includeStack:
        if a == f2:
          isRecursive = true
          break

      if not isRecursive:
        var buf = parseFile(f2, c.g.config.paths)
        c.includeStack.add f2
        #c.m.includes.add f2
        var n = cursorAt(buf, 0)
        semStmt(c, n)
        c.includeStack.setLen c.includeStack.len - 1
      else:
        var m = ""
        for i in 0..<c.includeStack.len:
          m.add c.includeStack[i]
          m.add " -> "
        m.add f2
        c.buildErr info, "recursive include: " & m

  producesVoid c, info, it.typ

proc importSingleFile(c: var SemContext; f1, origin: string; info: PackedLineInfo) =
  let f2 = resolveFile(c, origin, f1)
  let suffix = moduleSuffix(f2, c.g.config.paths)
  if not c.processedModules.containsOrIncl(suffix):
    if needsRecompile(f2, suffix):
      exec os.getAppFilename() & " m " & quoteShell(f2)

    loadInterface suffix, c.importTab

proc cyclicImport(c: var SemContext; x: var Cursor) =
  c.buildErr x.info, "cyclic module imports are not implemented"

proc semImport(c: var SemContext; it: var Item) =
  let info = it.n.info
  var x = it.n
  takeTree c, it.n
  inc x # skip the `import`

  if x.kind == ParLe and x == "pragmax":
    inc x
    var y = x
    skip y
    if y.substructureKind == PragmasS:
      inc y
      if y.kind == Ident and pool.strings[y.litId] == "cyclic":
        cyclicImport(c, x)
        return

  var files: seq[string] = @[]
  var hasError = false
  filenameVal(x, files, hasError)
  if hasError:
    c.buildErr info, "wrong `import` statement"
  else:
    let origin = getFile(c, info)
    for f in files:
      importSingleFile c, f, origin, info

  producesVoid c, info, it.typ

# -------------------- declare `result` -------------------------

proc classifyType(c: var SemContext; n: Cursor): TypeKind =
  result = typeKind(n)

proc declareResult(c: var SemContext; info: PackedLineInfo): SymId =
  if c.routine.kind in {ProcY, FuncY, ConverterY, MethodY, MacroY} and
      classifyType(c, c.routine.returnType) != VoidT:
    let name = pool.strings.getOrIncl("result")
    result = identToSym(c, name, ResultY)
    let s = Sym(kind: ResultY, name: result,
                pos: c.dest.len)
    discard c.currentScope.addNonOverloadable(name, s)

    let declStart = c.dest.len
    buildTree c.dest, ResultS, info:
      c.dest.add toToken(SymbolDef, result, info) # name
      c.dest.addDotToken() # export marker
      c.dest.addDotToken() # pragmas
      # XXX ^ pragma should be `.noinit` if the proc decl has it
      c.dest.copyTree(c.routine.returnType) # type
      c.dest.addDotToken() # value
    publish c, result, declStart
  else:
    result = SymId(0)

# -------------------- generics ---------------------------------

type
  SubsContext = object
    newVars: Table[SymId, SymId]
    params: ptr Table[SymId, Cursor]

proc subs(c: var SemContext; dest: var TokenBuf; sc: var SubsContext; body: Cursor) =
  var nested = 0
  var n = body
  while true:
    case n.kind
    of UnknownToken, EofToken, DotToken, Ident, StringLit, CharLit, IntLit, UIntLit, FloatLit:
      dest.add n
    of Symbol:
      let s = n.symId
      let arg = sc.params[].getOrDefault(s)
      if arg != default(Cursor):
        dest.addSubtree arg
      else:
        let nv = sc.newVars.getOrDefault(s)
        if nv != SymId(0):
          dest.add toToken(Symbol, nv, n.info)
        else:
          dest.add n # keep Symbol as it was
    of SymbolDef:
      let s = n.symId
      var isGlobal = false
      var name = extractBasename(pool.syms[s], isGlobal)
      if isGlobal:
        c.makeGlobalSym(name)
      else:
        c.makeLocalSym(name)
      let newDef = pool.syms.getOrIncl(name)
      sc.newVars[s] = newDef
      dest.add toToken(SymbolDef, newDef, n.info)
    of ParLe:
      dest.add n
      inc nested
    of ParRi:
      dest.add n
      dec nested
      if nested == 0: break
    inc n

proc produceInvoke(c: var SemContext; dest: var TokenBuf; req: InstRequest;
                   typeVars: Cursor; info: PackedLineInfo) =
  dest.buildTree InvokeT, info:
    dest.add toToken(Symbol, req.origin, info)
    var typeVars = typeVars
    if typeVars.substructureKind == TypevarsS:
      while typeVars.kind != ParRi:
        if typeVars.symKind == TypeVarY:
          var tv = typeVars
          inc tv
          dest.copyTree req.inferred[tv.symId]
        skip typeVars

proc subsGenericType(c: var SemContext; dest: var TokenBuf; req: InstRequest) =
  #[
  What we need to do is rather simple: A generic instantiation is
  the typical (type :Name ex generic_params pragmas body) tuple but
  this time the generic_params list the used `Invoke` construct for the
  instantiation.
  ]#
  let info = req.requestFrom[^1]
  let decl = getTypeSection(req.origin)
  dest.buildTree TypeS, info:
    dest.add toToken(SymbolDef, req.targetSym, info)
    dest.addDotToken() # export
    produceInvoke c, dest, req, decl.typevars, info
    # take the pragmas from the origin:
    dest.copyTree decl.pragmas
    var sc = SubsContext(params: addr req.inferred)
    subs(c, dest, sc, decl.body)

proc subsGenericProc(c: var SemContext; dest: var TokenBuf; req: InstRequest) =
  let info = req.requestFrom[^1]
  let decl = getProcDecl(req.origin)
  dest.buildTree decl.kind, info:
    dest.add toToken(SymbolDef, req.targetSym, info)
    if decl.exported.kind == ParLe:
      # magic?
      dest.copyTree decl.exported
    else:
      dest.addDotToken()
    dest.copyTree decl.pattern
    produceInvoke c, dest, req, decl.typevars, info

    var sc = SubsContext(params: addr req.inferred)
    subs(c, dest, sc, decl.params)
    subs(c, dest, sc, decl.retType)
    subs(c, dest, sc, decl.effects)
    subs(c, dest, sc, decl.pragmas)
    subs(c, dest, sc, decl.body)

template withFromInfo(req: InstRequest; body: untyped) =
  let oldLen = c.instantiatedFrom.len
  for jnfo in items(req.requestFrom):
    pushErrorContext c, jnfo
  body
  shrink c.instantiatedFrom, oldLen

proc semTypeSection(c: var SemContext; n: var Cursor)
proc instantiateGenericType(c: var SemContext; req: InstRequest) =
  var dest = createTokenBuf(30)
  withFromInfo req:
    subsGenericType c, dest, req
    var n = beginRead(dest)
    semTypeSection c, n

proc semProc(c: var SemContext; it: var Item; kind: SymKind)
proc instantiateGenericProc(c: var SemContext; req: InstRequest) =
  var dest = createTokenBuf(40)
  withFromInfo req:
    subsGenericProc c, dest, req
    var it = Item(n: beginRead(dest), typ: c.types.autoType)
    semProc c, it, it.n.symKind

proc instantiateGenerics(c: var SemContext) =
  while c.typeRequests.len + c.procRequests.len > 0:
    # This way with `move` ensures it is safe even though
    # the semchecking of generics can add to `c.typeRequests`
    # or to `c.procRequests`. This is subtle!
    let typeReqs = move(c.typeRequests)
    for t in typeReqs: instantiateGenericType c, t
    let procReqs = move(c.procRequests)
    for p in procReqs: instantiateGenericProc c, p

# -------------------- sem checking -----------------------------

type
  SemFlag = enum
    KeepMagics

proc semExpr(c: var SemContext; it: var Item; flags: set[SemFlag] = {})

proc semSymUse(c: var SemContext; s: SymId): Sym =
  # yyy find a better solution
  var name = pool.syms[s]
  extractBasename name
  let identifier = pool.strings.getOrIncl(name)
  var it {.cursor.} = c.currentScope
  while it != nil:
    for sym in it.tab.getOrDefault(identifier):
      if sym.name == s:
        return sym
    it = it.up

  let res = tryLoadSym(s)
  if res.status == LacksNothing:
    result = Sym(kind: symKind(res.decl), name: s, pos: ImportedPos)
  else:
    result = Sym(kind: NoSym, name: s, pos: InvalidPos)

proc semBoolExpr(c: var SemContext; it: var Item) =
  semExpr c, it
  if classifyType(c, it.typ) != BoolT:
    buildErr c, it.n.info, "expected `bool` but got: " & typeToString(it.typ)

proc semConstStrExpr(c: var SemContext; n: var Cursor) =
  # XXX check for constant
  var it = Item(n: n, typ: c.types.autoType)
  semExpr c, it
  n = it.n
  if classifyType(c, it.typ) != StringT:
    buildErr c, it.n.info, "expected `string` but got: " & typeToString(it.typ)

proc semConstIntExpr(c: var SemContext; n: var Cursor) =
  # XXX check for constant
  var it = Item(n: n, typ: c.types.autoType)
  semExpr c, it
  n = it.n
  if classifyType(c, it.typ) != IntT:
    buildErr c, it.n.info, "expected `int` but got: " & typeToString(it.typ)

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

proc implicitlyDiscardable(n: Cursor): bool =
  template checkBranch(branch) =
    if not implicitlyDiscardable(branch):
      return false

  var it = n
  #const
  #  skipForDiscardable = {nkStmtList, nkStmtListExpr,
  #    nkOfBranch, nkElse, nkFinally, nkExceptBranch,
  #    nkElifBranch, nkElifExpr, nkElseExpr, nkBlockStmt, nkBlockExpr,
  #    nkHiddenStdConv, nkHiddenSubConv, nkHiddenDeref}
  while it.kind == ParLe and stmtKind(it) in {StmtsS, BlockS}:
    inc it
    var last = it
    while true:
      skip it
      if it.kind == ParRi:
        it = last
        break
      else:
        last = it

  if it.kind != ParLe: return false
  case stmtKind(it)
  of IfS:
    inc it
    while it.kind != ParRi:
      case it.substructureKind
      of ElifS:
        inc it
        skip it # condition
        checkBranch(it)
        skip it
        skipParRi it
      of ElseS:
        inc it
        checkBranch(it)
        skip it
        skipParRi it
      else:
        error "illformed AST: `elif` or `else` inside `if` expected, got ", it
    # all branches are discardable
    result = true
  of CaseS:
    inc it
    while it.kind != ParRi:
      case it.substructureKind
      of OfS:
        inc it
        skip it # ranges
        checkBranch(it)
        skip it
        skipParRi it
      of ElifS:
        inc it
        skip it # condition
        checkBranch(it)
        skip it
        skipParRi it
      of ElseS:
        inc it
        checkBranch(it)
        skip it
        skipParRi it
      else:
        error "illformed AST: `of`, `elif` or `else` inside `case` expected, got ", it
    # all branches are discardable
    result = true
  #of TryS:
  #  checkBranch(it[0])
  #  for i in 1 ..< it.len:
  #    let branch = it[i]
  #    if branch.kind != nkFinally:
  #      checkBranch(branch[^1])
  #  # all branches are discardable
  #  result = true
  of CallS, CmdS:
    inc it
    if it.kind == Symbol:
      let sym = tryLoadSym(it.symId)
      if sym.status == LacksNothing:
        var decl = sym.decl
        if isRoutine(symKind(decl)):
          inc decl
          skip decl # name
          skip decl # exported
          skip decl # pattern
          skip decl # typevars
          skip decl # params
          skip decl # retType
          # decl should now be pragmas:
          inc decl
          while decl.kind != ParRi:
            if pragmaKind(decl) in {Discardable, NoReturn}:
              return true
            skip decl
    result = false
  of RetS, BreakS, ContinueS: # XXX also `raise`
    result = true
  else:
    result = false

proc semStmt(c: var SemContext; n: var Cursor) =
  let info = n.info
  var it = Item(n: n, typ: c.types.autoType)
  let exPos = c.dest.len
  semExpr c, it
  if classifyType(c, it.typ) in {NoType, VoidT, AutoT}:
    discard "ok"
  else:
    # analyze the expression that was just produced:
    let ex = cursorAt(c.dest, exPos)
    let discardable = implicitlyDiscardable(ex)
    endRead(c.dest)
    if discardable:
      combineType c, info, it.typ, c.types.voidType
    else:
      buildErr c, info, "expression of type `" & typeToString(it.typ) & "` must be discarded"
  n = it.n

template emptyNode(): Cursor =
  # XXX find a better solution for this
  c.types.voidType

template skipToLocalType(n) =
  inc n # skip ParLe
  inc n # skip name
  skip n # skip export marker
  skip n # skip pragmas

template skipToParams(n) =
  inc n # skip ParLe
  skip n # skip name
  skip n # skip export marker
  skip n # skip pattern
  skip n # skip generics

proc fetchType(c: var SemContext; it: var Item; s: Sym) =
  if s.kind == NoSym:
    c.buildErr it.n.info, "undeclared identifier"
    it.typ = c.types.autoType
  else:
    let res = declToCursor(c, s)
    if res.status == LacksNothing:
      var n = res.decl
      if s.kind.isLocal:
        skipToLocalType n
      elif s.kind.isRoutine:
        skipToParams n
      else:
        # XXX enum field, object field?
        assert false, "not implemented"
      it.typ = n
    else:
      c.buildErr it.n.info, "could not load symbol: " & pool.syms[s.name] & "; errorCode: " & $res.status
      it.typ = c.types.autoType

proc pickBestMatch(c: var SemContext; m: openArray[Match]): int =
  result = -1
  for i in 0..<m.len:
    if not m[i].err:
      if result < 0:
        result = i
      else:
        case cmpMatches(m[result], m[i])
        of NobodyWins:
          result = -2 # ambiguous
          break
        of FirstWins:
          discard "result remains the same"
        of SecondWins:
          result = i

when false:
  proc semExpr2(c: var SemContext; it: var Item): TokenBuf =
    result = createTokenBuf(20)
    swap c.dest, result
    semExpr c, it
    swap c.dest, result

proc addFn(c: var SemContext; fn: Cursor; args: openArray[Item]) =
  var inlinedMagic = false
  if fn.kind == Symbol:
    let res = tryLoadSym(fn.symId)
    if res.status == LacksNothing:
      var n = res.decl
      inc n # skip the symbol kind
      if n.kind == SymbolDef:
        inc n # skip the SymbolDef
        if n.kind == ParLe:
          inlinedMagic = true
          # ^ export marker position has a `(`? If so, it is a magic!
          copyKeepLineInfo c.dest[c.dest.len-1], n.load # overwrite the `(call` node with the magic itself
          inc n
          if n.kind == IntLit:
            if pool.integers[n.intId] == TypedMagic:
              c.dest.addSubtree args[0].typ
            else:
              c.dest.add n
            inc n
          if n.kind != ParRi:
            error "broken `magic`: expected ')', but got: ", n
  if not inlinedMagic:
    c.dest.addSubtree fn

proc semCall(c: var SemContext; it: var Item) =
  let callNode = it.n
  inc it.n
  var dest = createTokenBuf(16)
  swap c.dest, dest
  var fn = Item(n: it.n, typ: c.types.autoType)
  semExpr(c, fn, {KeepMagics})
  it.n = fn.n
  var args: seq[Item] = @[]
  var argIndexes: seq[int] = @[]
  while it.n.kind != ParRi:
    var arg = Item(n: it.n, typ: c.types.autoType)
    argIndexes.add c.dest.len
    semExpr c, arg
    it.n = arg.n
    args.add arg
  assert args.len == argIndexes.len
  swap c.dest, dest
  fn.n = beginRead(dest)
  for i in 0 ..< args.len:
    args[i].n = cursorAt(dest, argIndexes[i])

  var m: seq[Match] = @[]
  if fn.n.exprKind in {OchoiceX, CchoiceX}:
    var f = fn.n
    inc f
    while f.kind != ParRi:
      if f.kind == Symbol:
        let s = semSymUse(c, f.symId)
        var candidate = Item(n: f, typ: c.types.autoType)
        fetchType c, candidate, s
        m.add createMatch()
        sigmatch(m[^1], candidate, args, emptyNode())
      else:
        buildErr c, fn.n.info, "`choice` node does not contain `symbol`"
      inc f
  elif fn.n.kind == Ident:
    # error should have been given above already:
    # buildErr c, fn.n.info, "attempt to call undeclared routine"
    discard
  else:
    m.add createMatch()
    sigmatch(m[^1], fn, args, emptyNode())
  let idx = pickBestMatch(c, m)

  c.dest.add callNode
  if idx >= 0:
    c.addFn m[idx].fn.n, args
    c.dest.add m[idx].args
    combineType c, callNode.info, it.typ, m[idx].returnType
  elif idx == -2:
    buildErr c, callNode.info, "ambiguous call"
  elif m.len > 0:
    # use the first error for now
    # XXX Improve error messages here
    c.dest.add m[0].args
  else:
    buildErr c, callNode.info, "undeclared identifier"
  wantParRi c, it.n

proc sameIdent(sym: SymId; str: StrId): bool =
  # XXX speed this up by using the `fieldCache` idea
  var name = pool.syms[sym]
  extractBasename(name)
  result = pool.strings.getOrIncl(name) == str

proc findObjField(t: Cursor; name: StrId; level = 0): ObjField =
  assert t == "object"
  var n = t
  inc n # skip `(object` token
  let baseType = n
  skip n # skip basetype
  while n.kind == ParLe and n.substructureKind == FldS:
    inc n # skip FldS
    if n.kind == SymbolDef and sameIdent(n.symId, name):
      let symId = n.symId
      inc n # skip name
      skip n # export marker
      skip n # pragmas
      return ObjField(sym: symId, level: level, typ: n)
    skip n # skip name
    skip n # export marker
    skip n # pragmas
    skip n # type
    skip n # value
  if baseType.kind == Symbol:
    result = findObjField(objtypeImpl(baseType.symId), name, level+1)
  else:
    result = ObjField(level: -1)

type
  DotExprMode = enum
    OrdinaryDot, AlsoTryDotCall, DotDontReportError

proc semDot(c: var SemContext; it: var Item; mode: DotExprMode) =
  takeToken c, it.n
  var a = Item(n: it.n, typ: c.types.autoType)
  semExpr c, a
  it.n = a.n
  let info = it.n.info
  let fieldName = getIdent(c, it.n)
  var isMatch = false
  if fieldName == StrId(0):
    c.buildErr it.n.info, "identifier after `.` expected"
  else:
    let t = skipModifier(a.typ)
    if t.kind == Symbol:
      let objType = objtypeImpl(t.symId)
      if objType.typeKind == ObjectT:
        let field = findObjField(objType, fieldName)
        if field.level >= 0:
          c.dest.add toToken(Symbol, field.sym, info)
          c.dest.add toToken(IntLit, pool.integers.getOrIncl(field.level), info)
          combineType c, info, it.typ, field.typ
          isMatch = true
        else:
          c.buildErr it.n.info, "undeclared field: " & pool.strings[fieldName]
      else:
        c.buildErr it.n.info, "object type exptected"
    else:
      c.buildErr it.n.info, "object type exptected"
  # skip optional inheritance depth:
  if it.n.kind == IntLit:
    inc it.n
  wantParRi c, it.n

proc semWhile(c: var SemContext; it: var Item) =
  let info = it.n.info
  takeToken c, it.n
  semBoolExpr c, it
  inc c.routine.inLoop
  withNewScope c:
    semStmt c, it.n
  dec c.routine.inLoop
  wantParRi c, it.n
  producesVoid c, info, it.typ

proc semBreak(c: var SemContext; it: var Item) =
  let info = it.n.info
  takeToken c, it.n
  if c.routine.inLoop+c.routine.inBlock == 0:
    buildErr c, it.n.info, "`break` only possible within a `while` or `block` statement"
  else:
    wantDot c, it.n
  wantParRi c, it.n
  producesVoid c, info, it.typ

proc semContinue(c: var SemContext; it: var Item) =
  let info = it.n.info
  takeToken c, it.n
  if c.routine.inLoop == 0:
    buildErr c, it.n.info, "`continue` only possible within a `while` statement"
  else:
    wantDot c, it.n
  wantParRi c, it.n
  producesVoid c, info, it.typ

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
    takeTree c, n
  else:
    buildErr c, n.info, "expected '.' or 'x' for an export marker"

proc insertType(c: var SemContext; typ: TypeCursor; patchPosition: int) =
  let t = skipModifier(typ)
  c.dest.insert t, patchPosition

proc patchType(c: var SemContext; typ: TypeCursor; patchPosition: int) =
  let t = skipModifier(typ)
  c.dest.replace t, patchPosition

type
  CrucialPragma* = object
    magic: string
    bits: int

proc semPragma(c: var SemContext; n: var Cursor; crucial: var CrucialPragma; kind: SymKind) =
  if n == "kv":
    inc n
  let pk = pragmaKind(n)
  case pk
  of NoPragma:
    if kind.isRoutine and (let cc = callConvKind(n); cc != NoCallConv):
      c.dest.add toToken(ParLe, pool.tags.getOrIncl($cc), n.info)
      inc n
      wantParRi c, n
    else:
      buildErr c, n.info, "expected pragma"
      inc n
      wantParRi c, n
      #skip n
  of Magic:
    c.dest.add toToken(ParLe, pool.tags.getOrIncl($pk), n.info)
    inc n
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
  of ImportC, ImportCpp, ExportC, Header:
    c.dest.add toToken(ParLe, pool.tags.getOrIncl($pk), n.info)
    inc n
    if n.kind != ParRi:
      semConstStrExpr c, n
    wantParRi c, n
  of Align, Bits:
    c.dest.add toToken(ParLe, pool.tags.getOrIncl($pk), n.info)
    inc n
    semConstIntExpr c, n
    wantParRi c, n
  of Nodecl, Selectany, Threadvar, Globalvar, Discardable, Noreturn:
    c.dest.add toToken(ParLe, pool.tags.getOrIncl($pk), n.info)
    c.dest.addParRi()
    inc n

proc semPragmas(c: var SemContext; n: var Cursor; crucial: var CrucialPragma; kind: SymKind) =
  if n.kind == DotToken:
    takeToken c, n
  elif n == "pragmas":
    takeToken c, n
    while n.kind != ParRi:
      semPragma c, n, crucial, kind
    wantParRi c, n
  else:
    buildErr c, n.info, "expected '.' or 'pragmas'"

proc semIdentImpl(c: var SemContext; n: var Cursor; ident: StrId): Sym =
  let insertPos = c.dest.len
  let info = n.info
  let count = buildSymChoice(c, ident, info, InnerMost)
  if count == 1:
    let sym = c.dest[insertPos+1].symId
    c.dest.shrink insertPos
    c.dest.add toToken(Symbol, sym, info)
    result = semSymUse(c, sym)
  else:
    result = Sym(kind: if count == 0: NoSym else: CchoiceY)

proc semIdent(c: var SemContext; n: var Cursor): Sym =
  result = semIdentImpl(c, n, n.litId)
  inc n

proc semQuoted(c: var SemContext; n: var Cursor): Sym =
  let nameId = unquote(n)
  result = semIdentImpl(c, n, nameId)

proc maybeInlineMagic(c: var SemContext; res: LoadResult) =
  if res.status == LacksNothing:
    var n = res.decl
    inc n # skip the symbol kind
    if n.kind == SymbolDef:
      inc n # skip the SymbolDef
      if n.kind == ParLe:
        # ^ export marker position has a `(`? If so, it is a magic!
        c.dest[c.dest.len-1] = n.load
        inc n
        while true:
          c.dest.add n
          if n.kind == ParRi: break
          inc n

proc semTypeSym(c: var SemContext; s: Sym; info: PackedLineInfo) =
  if s.kind in {TypeY, TypevarY}:
    let res = tryLoadSym(s.name)
    maybeInlineMagic c, res
  else:
    c.buildErr info, "type name expected, but got: " & pool.syms[s.name]

proc semParams(c: var SemContext; n: var Cursor)
proc semLocal(c: var SemContext; n: var Cursor; kind: SymKind)

type
  TypeDeclContext = enum
    InLocalDecl, InTypeSection, InObjectDecl, InParamDecl, InInheritanceDecl, InReturnTypeDecl, AllowValues,
    InGenericConstraint

proc semLocalTypeImpl(c: var SemContext; n: var Cursor; context: TypeDeclContext)

proc semObjectType(c: var SemContext; n: var Cursor) =
  takeToken c, n
  # inherits from?
  if n.kind == DotToken:
    takeToken c, n
  else:
    semLocalTypeImpl c, n, InLocalDecl
  # object fields:
  withNewScope c:
    while n.substructureKind == FldS:
      semLocal(c, n, FldY)
  wantParRi c, n

proc semEnumType(c: var SemContext; n: var Cursor) =
  takeToken c, n
  wantDot c, n
  while n.substructureKind == EfldS:
    semLocal(c, n, EfldY)
  wantParRi c, n

proc semConceptType(c: var SemContext; n: var Cursor) =
  # XXX implement me
  takeTree c, n

proc semLocalTypeImpl(c: var SemContext; n: var Cursor; context: TypeDeclContext) =
  let info = n.info
  case n.kind
  of Ident:
    let s = semIdent(c, n)
    semTypeSym c, s, info
  of Symbol:
    let s = semSymUse(c, n.symId)
    inc n
    semTypeSym c, s, info
  of ParLe:
    case typeKind(n)
    of NoType:
      if exprKind(n) == QuotedX:
        let s = semQuoted(c, n)
        semTypeSym c, s, info
      elif context == AllowValues:
        var it = Item(n: n, typ: c.types.autoType)
        semExpr c, it
        n = it.n
      else:
        c.buildErr info, "not a type"
    of IntT, FloatT, CharT, BoolT, UIntT, VoidT, StringT, NilT, AutoT, SymKindT:
      takeTree c, n
    of PtrT, RefT, MutT, OutT, LentT, SinkT, NotT, UncheckedArrayT, SetT, StaticT, TypedescT:
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
  of DotToken:
    if context == InReturnTypeDecl:
      takeToken c, n
    else:
      c.buildErr info, "not a type"
  else:
    c.buildErr info, "not a type"

proc semLocalType(c: var SemContext; n: var Cursor; context = InLocalDecl): TypeCursor =
  let insertPos = c.dest.len
  semLocalTypeImpl c, n, context
  result = typeToCursor(c, insertPos)

proc semReturnType(c: var SemContext; n: var Cursor): TypeCursor =
  result = semLocalType(c, n, InReturnTypeDecl)

proc exportMarkerBecomesNifTag(c: var SemContext; insertPos: int; crucial: CrucialPragma) =
  assert crucial.magic.len > 0
  let info = c.dest[insertPos].info
  c.dest[insertPos] = toToken(ParLe, pool.tags.getOrIncl(crucial.magic), info)
  if crucial.bits != 0:
    let arr = [toToken(IntLit, pool.integers.getOrIncl(crucial.bits), info),
               toToken(ParRi, 0'u32, info)]
    c.dest.insert arr, insertPos+1
  else:
    let arr = [toToken(ParRi, 0'u32, info)]
    c.dest.insert arr, insertPos+1

proc semLocal(c: var SemContext; n: var Cursor; kind: SymKind) =
  let declStart = c.dest.len
  takeToken c, n
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
  of ParamY, LetY, VarY, CursorY, ResultY, FldY, EfldY:
    let beforeType = c.dest.len
    if n.kind == DotToken:
      # no explicit type given:
      inc n # 3
      var it = Item(n: n, typ: c.types.autoType)
      semExpr c, it # 4
      n = it.n
      insertType c, it.typ, beforeType
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
  publish c, delayed.s.name, declStart

proc semLocal(c: var SemContext; it: var Item; kind: SymKind) =
  let info = it.n.info
  semLocal c, it.n, kind
  producesVoid c, info, it.typ

proc semGenericParam(c: var SemContext; n: var Cursor) =
  if n == "typevar":
    semLocal c, n, TypevarY
  else:
    buildErr c, n.info, "expected 'typevar'"

proc semGenericParams(c: var SemContext; n: var Cursor) =
  if n.kind == DotToken:
    takeToken c, n
  elif n == "typevars":
    inc c.routine.inGeneric
    takeToken c, n
    while n.kind != ParRi:
      semGenericParam c, n
    wantParRi c, n
  else:
    buildErr c, n.info, "expected '.' or 'typevars'"

proc semParam(c: var SemContext; n: var Cursor) =
  if n == "param":
    semLocal c, n, ParamY
  else:
    buildErr c, n.info, "expected 'param'"

proc semParams(c: var SemContext; n: var Cursor) =
  if n.kind == DotToken:
    takeToken c, n
  elif n == "params":
    inc c.routine.inGeneric
    takeToken c, n
    while n.kind != ParRi:
      semParam c, n
    wantParRi c, n
  else:
    buildErr c, n.info, "expected '.' or 'params'"

proc addReturnResult(c: var SemContext; resId: SymId; info: PackedLineInfo) =
  if resId != SymId(0):
    assert c.dest[c.dest.len-1].kind == ParRi
    c.dest.shrink c.dest.len-1 # remove the ParRi
    # maybe add `return result`:
    buildTree(c.dest, RetS, info):
      c.dest.addSymUse resId, info
    c.dest.addParRi() # add it back

proc semProc(c: var SemContext; it: var Item; kind: SymKind) =
  let info = it.n.info
  let declStart = c.dest.len
  takeToken c, it.n
  let symId = declareOverloadableSym(c, it, kind)

  let beforeExportMarker = c.dest.len
  wantExportMarker c, it.n
  if it.n.kind == DotToken:
    takeToken c, it.n
  else:
    buildErr c, it.n.info, "TR pattern not implemented"
    skip it.n
  c.routine = createSemRoutine(kind, c.routine)
  try:
    c.openScope() # open parameter scope
    semGenericParams c, it.n
    semParams c, it.n
    c.routine.returnType = semReturnType(c, it.n)
    var crucial = default CrucialPragma
    semPragmas c, it.n, crucial, kind
    if crucial.magic.len > 0:
      exportMarkerBecomesNifTag c, beforeExportMarker, crucial
    if it.n.kind == DotToken:
      takeToken c, it.n
    else:
      buildErr c, it.n.info, "`effects` must be empty"
      skip it.n

    publishSignature c, symId, declStart
    if it.n.kind != DotToken:
      c.openScope() # open body scope
      let resId = declareResult(c, it.n.info)
      semProcBody c, it
      c.closeScope() # close body scope
      c.closeScope() # close parameter scope
      addReturnResult c, resId, it.n.info
    else:
      takeToken c, it.n
      c.closeScope() # close parameter scope
  finally:
    c.routine = c.routine.parent
  wantParRi c, it.n
  producesVoid c, info, it.typ
  publish c, symId, declStart

proc semStmts(c: var SemContext; it: var Item) =
  var info = it.n.info
  takeToken c, it.n
  while it.n.kind != ParRi:
    info = it.n.info
    semStmt c, it.n
  wantParRi c, it.n
  producesVoid c, info, it.typ

proc semExprSym(c: var SemContext; it: var Item; s: Sym; flags: set[SemFlag]) =
  if s.kind == NoSym:
    c.buildErr it.n.info, "undeclared identifier"
    it.typ = c.types.autoType
  elif s.kind == CchoiceY:
    if KeepMagics notin flags:
      c.buildErr it.n.info, "ambiguous identifier"
    it.typ = c.types.autoType
  elif s.kind in {TypeY, TypevarY}:
    let start = c.dest.len
    c.dest.buildTree TypedescT, it.n.info:
      c.dest.add toToken(Symbol, s.name, it.n.info)
      semTypeSym c, s, it.n.info
    it.typ = typeToCursor(c, start)
    c.dest.shrink start
  else:
    let res = declToCursor(c, s)
    if KeepMagics notin flags:
      maybeInlineMagic c, res
    if res.status == LacksNothing:
      var n = res.decl
      if s.kind.isLocal:
        skipToLocalType n
      elif s.kind.isRoutine:
        skipToParams n
      else:
        # XXX enum field?
        assert false, "not implemented"
      it.typ = n
    else:
      c.buildErr it.n.info, "could not load symbol: " & pool.syms[s.name] & "; errorCode: " & $res.status
      it.typ = c.types.autoType

proc semAsgn(c: var SemContext; it: var Item) =
  let info = it.n.info
  takeToken c, it.n
  var a = Item(n: it.n, typ: c.types.autoType)
  semExpr c, a # infers type of `left-hand-side`
  semExpr c, a # ensures type compatibility with `left-hand-side`
  it.n = a.n
  wantParRi c, it.n
  producesVoid c, info, it.typ

proc semEmit(c: var SemContext; it: var Item) =
  let info = it.n.info
  takeToken c, it.n
  while it.n.kind != ParRi:
    var a = Item(n: it.n, typ: c.types.autoType)
    semExpr c, a
    it.n = a.n
  wantParRi c, it.n
  producesVoid c, info, it.typ

proc semDiscard(c: var SemContext; it: var Item) =
  let info = it.n.info
  takeToken c, it.n
  if it.n.kind == DotToken:
    takeToken c, it.n
  else:
    var a = Item(n: it.n, typ: c.types.autoType)
    semExpr c, a
    it.n = a.n
    if classifyType(c, it.typ) == VoidT:
      buildErr c, it.n.info, "expression of type `" & typeToString(it.typ) & "` must not be discarded"
  wantParRi c, it.n
  producesVoid c, info, it.typ

proc semIf(c: var SemContext; it: var Item) =
  let info = it.n.info
  takeToken c, it.n
  if it.n.substructureKind == ElifS:
    while it.n.substructureKind == ElifS:
      takeToken c, it.n
      semBoolExpr c, it
      withNewScope c:
        semStmt c, it.n
      wantParRi c, it.n
  else:
    buildErr c, it.n.info, "illformed AST: `elif` inside `if` expected"
  if it.n.substructureKind == ElseS:
    takeToken c, it.n
    withNewScope c:
      semStmt c, it.n
    wantParRi c, it.n
  wantParRi c, it.n
  producesVoid c, info, it.typ

proc semReturn(c: var SemContext; it: var Item) =
  let info = it.n.info
  takeToken c, it.n
  if c.routine.kind == NoSym:
    buildErr c, it.n.info, "`return` only allowed within a routine"
  if it.n.kind == DotToken:
    takeToken c, it.n
  else:
    var a = Item(n: it.n, typ: c.routine.returnType)
    semExpr c, a
    it.n = a.n
  wantParRi c, it.n
  producesVoid c, info, it.typ

proc semYield(c: var SemContext; it: var Item) =
  let info = it.n.info
  takeToken c, it.n
  if c.routine.kind != IterY:
    buildErr c, it.n.info, "`yield` only allowed within an `iterator`"
  if it.n.kind == DotToken:
    takeToken c, it.n
  else:
    var a = Item(n: it.n, typ: c.routine.returnType)
    semExpr c, a
    it.n = a.n
  wantParRi c, it.n
  producesVoid c, info, it.typ

proc semTypeSection(c: var SemContext; n: var Cursor) =
  let declStart = c.dest.len
  takeToken c, n
  # name, export marker, generic params, pragmas, body
  let delayed = handleSymDef(c, n, TypeY) # 0
  let beforeExportMarker = c.dest.len
  wantExportMarker c, n # 1

  var crucial = default CrucialPragma
  semPragmas c, n, crucial, TypeY # 2
  if crucial.magic.len > 0:
    exportMarkerBecomesNifTag c, beforeExportMarker, crucial

  var isGeneric: bool
  if n.kind == DotToken:
    takeToken c, n
    isGeneric = false
  else:
    openScope c
    semGenericParams c, n
    isGeneric = true

  if n.kind == DotToken:
    takeToken c, n
  else:
    # body
    semLocalTypeImpl c, n, InTypeSection
  if isGeneric:
    closeScope c
  c.addSym delayed
  wantParRi c, n
  publish c, delayed.s.name, declStart

proc semExpr(c: var SemContext; it: var Item; flags: set[SemFlag] = {}) =
  case it.n.kind
  of IntLit:
    combineType c, it.n.info, it.typ, c.types.intType
    takeToken c, it.n
  of UIntLit:
    combineType c, it.n.info, it.typ, c.types.uintType
    takeToken c, it.n
  of FloatLit:
    combineType c, it.n.info, it.typ, c.types.floatType
    takeToken c, it.n
  of StringLit:
    combineType c, it.n.info, it.typ, c.types.stringType
    takeToken c, it.n
  of CharLit:
    combineType c, it.n.info, it.typ, c.types.charType
    takeToken c, it.n
  of Ident:
    let s = semIdent(c, it.n)
    semExprSym c, it, s, flags
  of Symbol:
    let s = semSymUse(c, it.n.symId)
    inc it.n
    semExprSym c, it, s, flags
  of ParLe:
    case exprKind(it.n)
    of QuotedX:
      let s = semQuoted(c, it.n)
      semExprSym c, it, s, flags
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
      of ContinueS: semContinue c, it
      of CallS, CmdS: semCall c, it
      of IncludeS: semInclude c, it
      of ImportS: semImport c, it
      of AsgnS: semAsgn c, it
      of EmitS: semEmit c, it
      of DiscardS: semDiscard c, it
      of IfS: semIf c, it
      of RetS: semReturn c, it
      of YieldS: semYield c, it
      of TypeS:
        let info = it.n.info
        semTypeSection c, it.n
        producesVoid c, info, it.typ
      of BlockS, ForS, CaseS, TemplateS:
        discard "XXX to implement"
    of FalseX, TrueX:
      combineType c, it.n.info, it.typ, c.types.boolType
      takeToken c, it.n
      wantParRi c, it.n
    of InfX, NegInfX, NanX:
      combineType c, it.n.info, it.typ, c.types.floatType
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
    of CallX, CmdX, CallStrLitX, InfixX, PrefixX:
      semCall c, it
    of DotX:
      semDot c, it, AlsoTryDotCall
    of AconstrX, AtX, DerefX, PatX, AddrX, NilX, NegX, SizeofX, OconstrX, KvX,
       AddX, SubX, MulX, DivX, ModX, ShrX, ShlX, BitandX, BitorX, BitxorX, BitnotX,
       EqX, NeqX, LeX, LtX, CastX, ConvX, SufX, RangeX, RangesX,
       HderefX, HaddrX, OconvX, HconvX, OchoiceX, CchoiceX,
       TupleConstrX, SetX,
       CompilesX, DeclaredX, DefinedX, HighX, LowX, TypeofX, AshrX:
      # XXX To implement
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
  writeFile outfile, "(.nif24)\n" & toString(c.dest)
  createIndex outfile

type
  ModuleFlag* = enum
    IsSystem, IsMain, SkipSystem

proc semcheck*(infile, outfile: string; config: sink NifConfig; moduleFlags: set[ModuleFlag]) =
  var n = setupProgram(infile, outfile)
  var c = SemContext(
    dest: createTokenBuf(),
    types: createBuiltinTypes(),
    thisModuleSuffix: prog.main,
    g: ProgramContext(config: config),
    routine: SemRoutine(kind: NoSym))
  c.currentScope = Scope(tab: initTable[StrId, seq[Sym]](), up: nil, kind: ToplevelScope)

  semStmt c, n
  #if n.kind != EofToken:
  #  quit "Internal error: file not processed completely"
  instantiateGenerics c
  if reportErrors(c) == 0:
    writeOutput c, outfile
