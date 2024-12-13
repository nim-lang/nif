#       Nimony
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Semantic checking:
## Most important task is to turn identifiers into symbols and to perform
## type checking.

import std / [tables, sets, syncio, formatfloat, assertions]
include nifprelude
import nimony_model, symtabs, builtintypes, decls, symparser,
  programs, sigmatch, magics, reporters, nifconfig, nifindexes,
  intervals, xints,
  semdata, semos, expreval

import ".." / gear2 / modnames

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

proc buildLocalErr*(dest: var TokenBuf; info: PackedLineInfo; msg: string) =
  when defined(debug):
    writeStackTrace()
    echo infoToStr(info) & " Error: " & msg
    quit msg
  dest.buildTree ErrT, info:
    dest.add toToken(StringLit, pool.strings.getOrIncl(msg), info)

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
  let isAtom = a.kind != ParLe
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
    if isAtom: return true
    inc a
    inc b
  return false

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

proc symToIdent(s: SymId): StrId =
  var name = pool.syms[s]
  extractBasename name
  result = pool.strings.getOrIncl name

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
    let s = Sym(kind: kind, name: n.symId, pos: c.dest.len)
    result = DelayedSym(status: OkExisting, s: s, info: info)
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
  assert s != SymId(0)
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
    inc n
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

# ------------------ include/import handling ------------------------

proc semStmt(c: var SemContext; n: var Cursor)

proc typeMismatch(c: var SemContext; info: PackedLineInfo; got, expected: TypeCursor) =
  c.buildErr info, "type mismatch: got: " & typeToString(got) & " but wanted: " & typeToString(expected)

proc typecheck(c: var SemContext; info: PackedLineInfo; got, expected: TypeCursor) =
  if sameTrees(expected, got):
    discard "fine"
  else:
    c.typeMismatch info, got, expected

proc combineType(c: var SemContext; info: PackedLineInfo; dest: var Cursor; src: Cursor) =
  if typeKind(dest) == AutoT:
    dest = src
  elif sameTrees(dest, src):
    discard "fine"
  else:
    c.typeMismatch info, src, dest

proc implicitlyDiscardable(n: Cursor, noreturnOnly = false): bool =
  template checkBranch(branch) =
    if not implicitlyDiscardable(branch, noreturnOnly):
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
          let accepted =
            if noreturnOnly: {NoReturn}
            else: {Discardable, NoReturn}
          while decl.kind != ParRi:
            if pragmaKind(decl) in accepted:
              return true
            skip decl
    result = false
  of RetS, BreakS, ContinueS: # XXX also `raise`
    result = true
  else:
    result = false

proc isNoReturn(n: Cursor): bool {.inline.} =
  result = implicitlyDiscardable(n, noreturnOnly = true)

proc commonType(c: var SemContext; it: var Item; argBegin: int; expected: TypeCursor) =
  if typeKind(expected) == AutoT:
    return
  elif typeKind(it.typ) == AutoT:
    it.typ = expected
    return

  let info = it.n.info
  var m = createMatch(addr c)
  var arg = Item(n: cursorAt(c.dest, argBegin), typ: it.typ)
  if typeKind(arg.typ) == VoidT and isNoReturn(arg.n):
    # noreturn allowed in expression context
    # maybe use sem flags to restrict this to statement branches
    discard
  else:
    typematch m, expected, arg
  endRead(c.dest)
  if m.err:
    when defined(debug):
      shrink c.dest, argBegin
      c.dest.add m.args
    else:
      c.typeMismatch info, it.typ, expected
  else:
    shrink c.dest, argBegin
    c.dest.add m.args
    it.typ = expected

proc producesVoid(c: var SemContext; info: PackedLineInfo; dest: var Cursor) =
  if typeKind(dest) in {AutoT, VoidT}:
    combineType c, info, dest, c.types.voidType
  else:
    c.typeMismatch info, c.types.voidType, dest

proc producesNoReturn(c: var SemContext; info: PackedLineInfo; dest: var Cursor) =
  if typeKind(dest) in {AutoT, VoidT}:
    combineType c, info, dest, c.types.voidType
  else:
    # allowed in expression context
    discard

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
          m.add shortenDir c.includeStack[i]
          m.add " -> "
        m.add shortenDir f2
        c.buildErr info, "recursive include: " & m

  producesVoid c, info, it.typ

proc importSingleFile(c: var SemContext; f1, origin: string; info: PackedLineInfo) =
  let f2 = resolveFile(c, origin, f1)
  let suffix = moduleSuffix(f2, c.g.config.paths)
  if not c.processedModules.containsOrIncl(suffix):
    if needsRecompile(f2, suffix):
      selfExec c, f2

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

proc newSymId(c: var SemContext; s: SymId): SymId =
  var isGlobal = false
  var name = extractBasename(pool.syms[s], isGlobal)
  if isGlobal:
    c.makeGlobalSym(name)
  else:
    c.makeLocalSym(name)
  result = pool.syms.getOrIncl(name)

type
  SubsContext = object
    newVars: Table[SymId, SymId]
    params: ptr Table[SymId, Cursor]

proc subs(c: var SemContext; dest: var TokenBuf; sc: var SubsContext; body: Cursor) =
  var nested = 0
  var n = body
  let isAtom = n.kind != ParLe
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
      let newDef = newSymId(c, s)
      sc.newVars[s] = newDef
      dest.add toToken(SymbolDef, newDef, n.info)
    of ParLe:
      dest.add n
      inc nested
    of ParRi:
      dest.add n
      dec nested
      if nested == 0: break
    if isAtom: break
    inc n

include templates

proc produceInvoke(c: var SemContext; dest: var TokenBuf; req: InstRequest;
                   typeVars: Cursor; info: PackedLineInfo) =
  dest.buildTree InvokeT, info:
    dest.add toToken(Symbol, req.origin, info)
    var typeVars = typeVars
    if typeVars.substructureKind == TypevarsS:
      inc typeVars
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

type
  PassKind = enum checkSignatures, checkBody, checkGenericInst, checkConceptProc

proc semProc(c: var SemContext; it: var Item; kind: SymKind; pass: PassKind)
proc instantiateGenericProc(c: var SemContext; req: InstRequest) =
  var dest = createTokenBuf(40)
  withFromInfo req:
    subsGenericProc c, dest, req
    var it = Item(n: beginRead(dest), typ: c.types.autoType)
    #echo "now in generic proc: ", toString(it.n)
    semProc c, it, it.n.symKind, checkGenericInst

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

proc fetchSym(c: var SemContext; s: SymId): Sym =
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

proc semBoolExpr(c: var SemContext; n: var Cursor) =
  var it = Item(n: n, typ: c.types.autoType)
  semExpr c, it
  n = it.n
  if classifyType(c, it.typ) != BoolT:
    buildErr c, it.n.info, "expected `bool` but got: " & typeToString(it.typ)

proc semConstBoolExpr(c: var SemContext; n: var Cursor) =
  let start = c.dest.len
  var it = Item(n: n, typ: c.types.autoType)
  semExpr c, it
  n = it.n
  if classifyType(c, it.typ) != BoolT:
    buildErr c, it.n.info, "expected `bool` but got: " & typeToString(it.typ)
  var e = cursorAt(c.dest, start)
  var valueBuf = evalExpr(e)
  endRead(c.dest)
  let value = cursorAt(valueBuf, 0)
  if not isConstBoolValue(value):
    if value.kind == ParLe and value.tagId == ErrT:
      c.dest.add valueBuf
    else:
      buildErr c, it.n.info, "expected constant bool value but got: " & toString(value, false)
  else:
    c.dest.shrink start
    c.dest.add valueBuf

proc semConstStrExpr(c: var SemContext; n: var Cursor) =
  let start = c.dest.len
  var it = Item(n: n, typ: c.types.autoType)
  semExpr c, it
  n = it.n
  if classifyType(c, it.typ) != StringT:
    buildErr c, it.n.info, "expected `string` but got: " & typeToString(it.typ)
  var e = cursorAt(c.dest, start)
  var valueBuf = evalExpr(e)
  endRead(c.dest)
  let value = cursorAt(valueBuf, 0)
  if not isConstStringValue(value):
    if value.kind == ParLe and value.tagId == ErrT:
      c.dest.add valueBuf
    else:
      buildErr c, it.n.info, "expected constant string value but got: " & toString(value, false)
  else:
    c.dest.shrink start
    c.dest.add valueBuf

proc semConstIntExpr(c: var SemContext; n: var Cursor) =
  let start = c.dest.len
  var it = Item(n: n, typ: c.types.autoType)
  semExpr c, it
  n = it.n
  if classifyType(c, it.typ) != IntT:
    buildErr c, it.n.info, "expected `int` but got: " & typeToString(it.typ)
  var e = cursorAt(c.dest, start)
  var valueBuf = evalExpr(e)
  endRead(c.dest)
  let value = cursorAt(valueBuf, 0)
  if not isConstIntValue(value):
    if value.kind == ParLe and value.tagId == ErrT:
      c.dest.add valueBuf
    else:
      buildErr c, it.n.info, "expected constant integer value but got: " & toString(value, false)
  else:
    c.dest.shrink start
    c.dest.add valueBuf

proc isLastSon(n: Cursor): bool =
  var n = n
  skip n
  result = n.kind == ParRi

proc semStmtsExprImpl(c: var SemContext; it: var Item) =
  while it.n.kind != ParRi:
    if not isLastSon(it.n):
      semStmt c, it.n
    else:
      semExpr c, it
  wantParRi c, it.n

proc semStmtsExpr(c: var SemContext; it: var Item) =
  takeToken c, it.n
  semStmtsExprImpl c, it

proc semProcBody(c: var SemContext; itB: var Item) =
  let beforeBodyPos = c.dest.len
  let info = itB.n.info
  var it = Item(n: itB.n, typ: c.types.autoType)
  semStmtsExprImpl c, it
  if c.routine.kind == TemplateY:
    typecheck(c, info, it.typ, c.routine.returnType)
  elif classifyType(c, it.typ) == VoidT:
    discard "ok"
  else:
    typecheck(c, info, it.typ, c.routine.returnType)
    # transform `expr` to `result = expr`:
    if c.routine.resId != SymId(0):
      var prefix = [
        toToken(ParLe, pool.tags.getOrIncl($AsgnS), info),
        toToken(Symbol, c.routine.resId, info)]
      c.dest.insert prefix, beforeBodyPos
      c.dest.addParRi()
  itB.n = it.n

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
    if not discardable:
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

proc fetchType(c: var SemContext; n: Cursor; s: Sym): TypeCursor =
  if s.kind == NoSym:
    c.buildErr n.info, "undeclared identifier"
    result = c.types.autoType
  else:
    let res = declToCursor(c, s)
    if res.status == LacksNothing:
      var d = res.decl
      if s.kind.isLocal:
        skipToLocalType d
      elif s.kind.isRoutine:
        skipToParams d
      else:
        # XXX enum field, object field?
        assert false, "not implemented"
      result = d
    else:
      c.buildErr n.info, "could not load symbol: " & pool.syms[s.name] & "; errorCode: " & $res.status
      result = c.types.autoType

proc pickBestMatch(c: var SemContext; m: openArray[Match]): int =
  result = -1
  var other = -1
  for i in 0..<m.len:
    if not m[i].err:
      if result < 0:
        result = i
      else:
        case cmpMatches(m[result], m[i])
        of NobodyWins:
          other = i
        of FirstWins:
          discard "result remains the same"
        of SecondWins:
          result = i
          other = -1
  if other >= 0: result = -2 # ambiguous

const
  ConceptProcY = CchoiceY

proc addFn(c: var SemContext; fn: FnCandidate; fnOrig: Cursor; args: openArray[Item]): bool =
  result = false
  if fn.kind in RoutineKinds:
    assert fn.sym != SymId(0)
    let res = tryLoadSym(fn.sym)
    if res.status == LacksNothing:
      var n = res.decl
      inc n # skip the symbol kind
      if n.kind == SymbolDef:
        inc n # skip the SymbolDef
        if n.kind == ParLe:
          result = true
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
    if not result:
      c.dest.add toToken(Symbol, fn.sym, fnOrig.info)
  elif fn.kind == ConceptProcY and fn.sym != SymId(0):
    c.dest.add toToken(Ident, symToIdent(fn.sym), fnOrig.info)
  else:
    c.dest.addSubtree fnOrig

proc semTemplateCall(c: var SemContext; it: var Item; fnId: SymId; beforeCall: int;
                    inferred: ptr Table[SymId, Cursor]) =
  var expandedInto = createTokenBuf(30)

  let s = fetchSym(c, fnId)
  let res = declToCursor(c, s)
  if res.status == LacksNothing:
    let args = cursorAt(c.dest, beforeCall+2)
    let firstVarargMatch = default(Cursor)
    # XXX implement varargs here
    expandTemplate(c, expandedInto, res.decl, args, firstVarargMatch, inferred)
    endRead(c.dest)
    shrink c.dest, beforeCall
    var a = Item(n: cursorAt(expandedInto, 0), typ: c.types.autoType)
    semExpr c, a
    it.typ = a.typ
    it.kind = a.kind
  else:
    c.buildErr it.n.info, "could not load symbol: " & pool.syms[fnId] & "; errorCode: " & $res.status

proc sameIdent(sym: SymId; str: StrId): bool =
  # XXX speed this up by using the `fieldCache` idea
  var name = pool.syms[sym]
  extractBasename(name)
  result = pool.strings.getOrIncl(name) == str

proc sameIdent(a, b: SymId): bool =
  # XXX speed this up by using the `fieldCache` idea
  var x = pool.syms[a]
  extractBasename(x)
  var y = pool.syms[b]
  extractBasename(y)
  result = x == y

type
  FnCandidates = object
    a: seq[FnCandidate]
    s: HashSet[SymId]

proc addUnique(c: var FnCandidates; x: FnCandidate) =
  if not containsOrIncl(c.s, x.sym):
    c.a.add x

proc maybeAddConceptMethods(c: var SemContext; fn: StrId; typevar: SymId; cands: var FnCandidates) =
  let res = tryLoadSym(typevar)
  assert res.status == LacksNothing
  let local = asLocal(res.decl)
  if local.kind == TypevarY and local.typ.kind == Symbol:
    let concpt = local.typ.symId
    let section = getTypeSection concpt

    var ops = section.body
    inc ops  # (concept
    skip ops # .
    skip ops # .
    skip ops #   (typevar Self ...)
    if ops == "stmts":
      inc ops
      while ops.kind != ParRi:
        let sk = ops.symKind
        if sk in RoutineKinds:
          var prc = ops
          inc prc # (proc
          if prc.kind == SymbolDef and sameIdent(prc.symId, fn):
            var d = ops
            skipToParams d
            cands.addUnique FnCandidate(kind: ConceptProcY, sym: prc.symId, typ: d)
        skip ops

proc considerTypeboundOps(c: var SemContext; m: var seq[Match]; candidates: FnCandidates; args: openArray[Item]) =
  for candidate in candidates.a:
    m.add createMatch(addr c)
    sigmatch(m[^1], candidate, args, emptyNode())

proc requestRoutineInstance(c: var SemContext; origin: SymId; m: var Match;
                            info: PackedLineInfo): ProcInstance =
  let key = typeToCanon(m.typeArgs, 0)
  result = c.instantiatedProcs.getOrDefault(key)
  if result.targetSym == SymId(0):
    let targetSym = newSymId(c, origin)
    var signature = createTokenBuf(30)
    let decl = getProcDecl(origin)
    assert decl.typevars == "typevars", pool.syms[origin]
    buildTree signature, decl.kind, info:
      signature.add toToken(SymbolDef, targetSym, info)
      signature.addDotToken() # a generic instance is not exported
      signature.copyTree decl.pattern
      # InvokeT for the generic params:
      signature.buildTree InvokeT, info:
        signature.add toToken(Symbol, origin, info)
        signature.add m.typeArgs
      var sc = SubsContext(params: addr m.inferred)
      subs(c, signature, sc, decl.params)
      let beforeRetType = signature.len
      subs(c, signature, sc, decl.retType)
      subs(c, signature, sc, decl.pragmas)
      subs(c, signature, sc, decl.effects)
      signature.addDotToken() # no body

    result = ProcInstance(targetSym: targetSym, procType: cursorAt(signature, 0),
      returnType: cursorAt(signature, beforeRetType))
    publish targetSym, ensureMove signature

    c.instantiatedProcs[key] = result
    var req = InstRequest(
      origin: origin,
      targetSym: targetSym,
      inferred: move(m.inferred)
    )
    for ins in c.instantiatedFrom: req.requestFrom.add ins
    req.requestFrom.add info

    c.procRequests.add ensureMove req

proc typeofCallIs(c: var SemContext; it: var Item; beforeCall: int; returnType: TypeCursor) {.inline.} =
  let expected = it.typ
  it.typ = returnType
  commonType c, it, beforeCall, expected

proc getFnIdent(c: var SemContext): StrId =
  var n = beginRead(c.dest)
  result = getIdent(c, n)
  endRead(c.dest)

proc semCall(c: var SemContext; it: var Item) =
  let beforeCall = c.dest.len
  let callNode = it.n.load()
  inc it.n
  var dest = createTokenBuf(16)
  swap c.dest, dest
  var fn = Item(n: it.n, typ: c.types.autoType)
  semExpr(c, fn, {KeepMagics})
  let fnKind = fn.kind
  let fnName = getFnIdent(c)
  it.n = fn.n
  var args: seq[Item] = @[]
  var argIndexes: seq[int] = @[]
  var candidates = default FnCandidates
  while it.n.kind != ParRi:
    var arg = Item(n: it.n, typ: c.types.autoType)
    argIndexes.add c.dest.len
    semExpr c, arg
    # scope extension: If the type is Typevar and it has attached
    # a concept, use the concepts symbols too:
    if fnName != StrId(0) and arg.typ.kind == Symbol:
      maybeAddConceptMethods c, fnName, arg.typ.symId, candidates
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
        let sym = f.symId
        let s = fetchSym(c, sym)
        let candidate = FnCandidate(kind: s.kind, sym: sym, typ: fetchType(c, f, s))
        m.add createMatch(addr c)
        sigmatch(m[^1], candidate, args, emptyNode())
      else:
        buildErr c, fn.n.info, "`choice` node does not contain `symbol`"
      inc f
    considerTypeboundOps(c, m, candidates, args)
  elif fn.n.kind == Ident:
    # error should have been given above already:
    # buildErr c, fn.n.info, "attempt to call undeclared routine"
    discard
  else:
    # Keep in mind that proc vars are a thing:
    let sym = if fn.n.kind == Symbol: fn.n.symId else: SymId(0)
    let candidate = FnCandidate(kind: fnKind, sym: sym, typ: fn.typ)
    m.add createMatch(addr c)
    sigmatch(m[^1], candidate, args, emptyNode())
    considerTypeboundOps(c, m, candidates, args)
  let idx = pickBestMatch(c, m)

  c.dest.add callNode
  if idx >= 0:
    let finalFn = m[idx].fn
    let isMagic = c.addFn(finalFn, fn.n, args)
    c.dest.add m[idx].args
    wantParRi c, it.n

    if finalFn.kind == TemplateY:
      typeofCallIs c, it, beforeCall, m[idx].returnType
      if c.templateInstCounter <= MaxNestedTemplates:
        inc c.templateInstCounter
        withErrorContext c, callNode.info:
          semTemplateCall c, it, finalFn.sym, beforeCall, addr m[idx].inferred
        dec c.templateInstCounter
      else:
        buildErr c, callNode.info, "recursion limit exceeded for template expansions"
    elif c.routine.inGeneric == 0 and m[idx].inferred.len > 0 and not isMagic:
      assert fn.n.kind == Symbol
      let inst = c.requestRoutineInstance(fn.n.symId, m[idx], callNode.info)
      c.dest[beforeCall+1].setSymId inst.targetSym
      typeofCallIs c, it, beforeCall, inst.returnType
    else:
      typeofCallIs c, it, beforeCall, m[idx].returnType

  elif idx == -2:
    buildErr c, callNode.info, "ambiguous call"
    wantParRi c, it.n
  elif m.len > 0:
    # use the first error for now
    # XXX Improve error messages here
    c.dest.add m[0].args
    wantParRi c, it.n
  else:
    buildErr c, callNode.info, "undeclared identifier"
    wantParRi c, it.n

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
  let exprStart = c.dest.len
  let expected = it.typ
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
          it.typ = field.typ # will be fit later with commonType
          it.kind = FldY
          isMatch = true
        else:
          c.buildErr it.n.info, "undeclared field: " & pool.strings[fieldName]
      else:
        c.buildErr it.n.info, "object type exptected"
    elif t.typeKind == TupleT:
      var tup = t
      inc tup
      while tup.kind != ParRi:
        let field = asLocal(tup)
        if field.name.kind == SymbolDef and sameIdent(field.name.symId, fieldName):
          c.dest.add toToken(Symbol, field.name.symId, info)
          it.typ = field.typ # will be fit later with commonType
          it.kind = FldY
          isMatch = true
          break
        skip tup
      c.dest.add toToken(IntLit, pool.integers.getOrIncl(0), info)
      if not isMatch:
        c.buildErr it.n.info, "undeclared field: " & pool.strings[fieldName]
    else:
      c.buildErr it.n.info, "object type exptected"
  # skip optional inheritance depth:
  if it.n.kind == IntLit:
    inc it.n
  wantParRi c, it.n
  if isMatch:
    commonType c, it, exprStart, expected

proc semWhile(c: var SemContext; it: var Item) =
  let info = it.n.info
  takeToken c, it.n
  semBoolExpr c, it.n
  inc c.routine.inLoop
  withNewScope c:
    semStmt c, it.n
  dec c.routine.inLoop
  wantParRi c, it.n
  producesVoid c, info, it.typ

proc semBlock(c: var SemContext; it: var Item) =
  let info = it.n.info
  takeToken c, it.n

  inc c.routine.inBlock
  withNewScope c:
    if it.n.kind == DotToken:
      takeToken c, it.n
    else:
      let declStart = c.dest.len
      let delayed = handleSymDef(c, it.n, LabelY)
      c.addSym delayed
      publish c, delayed.s.name, declStart

    semStmt c, it.n
  dec c.routine.inBlock

  wantParRi c, it.n
  producesVoid c, info, it.typ

proc semBreak(c: var SemContext; it: var Item) =
  let info = it.n.info
  takeToken c, it.n
  if c.routine.inLoop+c.routine.inBlock == 0:
    buildErr c, it.n.info, "`break` only possible within a `while` or `block` statement"
  else:
    if it.n.kind == DotToken:
      wantDot c, it.n
    else:
      var a = Item(n: it.n, typ: c.types.autoType)
      semExpr(c, a)
      if a.kind != LabelY:
        buildErr c, it.n.info, "`break` needs a block label"
      it.n = a.n
  wantParRi c, it.n
  producesNoReturn c, info, it.typ

proc semContinue(c: var SemContext; it: var Item) =
  let info = it.n.info
  takeToken c, it.n
  if c.routine.inLoop == 0:
    buildErr c, it.n.info, "`continue` only possible within a `while` statement"
  else:
    wantDot c, it.n
  wantParRi c, it.n
  producesNoReturn c, info, it.typ

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
  let pk = pragmaKind(n)
  case pk
  of NoPragma:
    if kind.isRoutine and (let cc = callConvKind(n); cc != NoCallConv):
      c.dest.add toToken(ParLe, pool.tags.getOrIncl($cc), n.info)
      inc n
      c.dest.addParRi()
    else:
      buildErr c, n.info, "expected pragma"
      inc n
      c.dest.addParRi()
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
    c.dest.addParRi()
  of ImportC, ImportCpp, ExportC, Header:
    c.dest.add toToken(ParLe, pool.tags.getOrIncl($pk), n.info)
    inc n
    if n.kind != ParRi:
      semConstStrExpr c, n
    c.dest.addParRi()
  of Align, Bits:
    c.dest.add toToken(ParLe, pool.tags.getOrIncl($pk), n.info)
    inc n
    semConstIntExpr(c, n)
    c.dest.addParRi()
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
      let isKeyValue = n == "kv"
      if isKeyValue:
        inc n
      semPragma c, n, crucial, kind
      if isKeyValue:
        skip n # skips ')'
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
    result = fetchSym(c, sym)
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

type
  TypeDeclContext = enum
    InLocalDecl, InTypeSection, InObjectDecl, InParamDecl, InInheritanceDecl, InReturnTypeDecl, AllowValues,
    InGenericConstraint

proc semLocalTypeImpl(c: var SemContext; n: var Cursor; context: TypeDeclContext)

proc semTypeSym(c: var SemContext; s: Sym; info: PackedLineInfo; context: TypeDeclContext) =
  if s.kind in {TypeY, TypevarY}:
    let res = tryLoadSym(s.name)
    let beforeMagic = c.dest.len
    maybeInlineMagic c, res
    let afterMagic = c.dest.len
    if s.kind == TypevarY:
      # likely was not magic
      # maybe substitution performed here?
      inc c.usedTypevars
    elif beforeMagic != afterMagic:
      # was magic, nothing to do
      discard
    else:
      let typ = asTypeDecl(res.decl)
      if typ.body.typeKind in {ObjectT, EnumT, DistinctT, ConceptT}:
        # types that should stay as symbols, see sigmatch.matchSymbol
        discard
      else:
        # remove symbol, inline type:
        c.dest.shrink c.dest.len-1
        var t = typ.body
        semLocalTypeImpl c, t, context
  elif s.kind != NoSym:
    c.buildErr info, "type name expected, but got: " & pool.syms[s.name]
  else:
    c.buildErr info, "unknown type name"

proc semParams(c: var SemContext; n: var Cursor)
proc semLocal(c: var SemContext; n: var Cursor; kind: SymKind)

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

proc semTupleType(c: var SemContext; n: var Cursor) =
  takeToken c, n
  # tuple fields:
  withNewScope c:
    while n.substructureKind == FldS:
      semLocal(c, n, FldY)
  wantParRi c, n

proc semEnumField(c: var SemContext; n: var Cursor; enumType: SymId)

proc semEnumType(c: var SemContext; n: var Cursor; enumType: SymId) =
  takeToken c, n
  while n.substructureKind == EfldS:
    semEnumField(c, n, enumType)
  wantParRi c, n

proc declareConceptSelf(c: var SemContext; info: PackedLineInfo) =
  let name = pool.strings.getOrIncl("Self")
  let result = identToSym(c, name, TypevarY)
  let s = Sym(kind: TypevarY, name: result,
              pos: c.dest.len)
  discard c.currentScope.addNonOverloadable(name, s)
  let declStart = c.dest.len
  buildTree c.dest, TypevarY, info:
    c.dest.add toToken(SymbolDef, result, info) # name
    c.dest.addDotToken() # export marker
    c.dest.addDotToken() # pragmas
    c.dest.addDotToken() # typ
    c.dest.addDotToken() # value
  publish c, result, declStart

proc semConceptType(c: var SemContext; n: var Cursor) =
  takeToken c, n
  wantDot c, n
  wantDot c, n
  declareConceptSelf c, n.info
  skip n # skip dot or previous `Self` declaration
  if n != "stmts":
    error "(stmts) expected, but got: ", n
  takeToken c, n
  withNewScope c:
    while true:
      let k = n.symKind
      if k in RoutineKinds:
        var it = Item(n: n, typ: c.types.voidType)
        semProc(c, it, k, checkConceptProc)
        n = it.n
      else:
        break
  wantParRi c, n
  wantParRi c, n

proc instGenericType(c: var SemContext; dest: var TokenBuf; info: PackedLineInfo;
                     origin, targetSym: SymId; decl: TypeDecl; args: Cursor) =
  #[
  What we need to do is rather simple: A generic instantiation is
  the typical (type :Name ex generic_params pragmas body) tuple but
  this time the generic_params list the used `Invoke` construct for the
  instantiation.
  ]#
  var inferred = initTable[SymId, Cursor]()
  var err = 0
  dest.buildTree TypeS, info:
    dest.add toToken(SymbolDef, targetSym, info)
    dest.addDotToken() # export
    dest.buildTree InvokeT, info:
      dest.add toToken(Symbol, origin, info)
      var a = args
      var typevars = decl.typevars
      inc typevars
      while a.kind != ParRi and typevars.kind != ParRi:
        var tv = typevars
        assert tv == "typevar"
        inc tv
        assert tv.kind == SymbolDef
        inferred[tv.symId] = a
        takeTree dest, a
        skip typevars
      if a.kind != ParRi:
        err = -1
      elif typevars.kind != ParRi:
        err = 1
    # take the pragmas from the origin:
    dest.copyTree decl.pragmas
    if err == 0:
      var sc = SubsContext(params: addr inferred)
      subs(c, dest, sc, decl.body)
    elif err == 1:
      dest.buildLocalErr info, "too few generic arguments provided"
    else:
      dest.buildLocalErr info, "too many generic arguments provided"

proc semInvoke(c: var SemContext; n: var Cursor) =
  let typeStart = c.dest.len
  let info = n.info
  takeToken c, n # copy `at`
  semLocalTypeImpl c, n, InLocalDecl

  var headId: SymId = SymId(0)
  var decl = default TypeDecl
  var ok = false
  if c.dest[typeStart+1].kind == Symbol:
    headId = c.dest[typeStart+1].symId
    decl = getTypeSection(headId)
    if decl.kind != TypeY:
      c.buildErr info, "cannot attempt to instantiate a non-type"
    if decl.typevars != "typevars":
      c.buildErr info, "cannot attempt to instantiate a concrete type"
    else:
      ok = true
  else:
    c.buildErr info, "cannot attempt to instantiate a non-type"

  var genericArgs = 0
  swap c.usedTypevars, genericArgs
  let beforeArgs = c.dest.len
  while n.kind != ParRi:
    semLocalTypeImpl c, n, AllowValues
  swap c.usedTypevars, genericArgs
  wantParRi c, n
  if genericArgs == 0 and ok:
    # we have to be eager in generic type instantiations so that type-checking
    # can do its job properly:
    let key = typeToCanon(c.dest, typeStart)
    if c.instantiatedTypes.hasKey(key):
      c.dest.add toToken(Symbol, c.instantiatedTypes[key], info)
    else:
      let targetSym = newSymId(c, headId)
      var args = cursorAt(c.dest, beforeArgs)
      var instance = createTokenBuf(30)
      instGenericType c, instance, info, headId, targetSym, decl, args
      c.dest.endRead()
      publish targetSym, ensureMove instance
      c.instantiatedTypes[key] = targetSym
      c.dest.shrink typeStart
      c.dest.add toToken(Symbol, targetSym, info)

proc semLocalTypeImpl(c: var SemContext; n: var Cursor; context: TypeDeclContext) =
  let info = n.info
  case n.kind
  of Ident:
    let s = semIdent(c, n)
    semTypeSym c, s, info, context
  of Symbol:
    let s = fetchSym(c, n.symId)
    inc n
    semTypeSym c, s, info, context
  of ParLe:
    case typeKind(n)
    of NoType:
      if exprKind(n) == QuotedX:
        let s = semQuoted(c, n)
        semTypeSym c, s, info, context
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
    of TupleT:
      semTupleType c, n
    of ArrayT:
      takeToken c, n
      semLocalTypeImpl c, n, context
      semLocalTypeImpl c, n, AllowValues
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
      c.buildErr info, "`enum` type must be defined in a `type` section"
      skip n
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
    of InvokeT:
      semInvoke c, n
  of DotToken:
    if context in {InReturnTypeDecl, InGenericConstraint}:
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
    discard semLocalType(c, n, InGenericConstraint)
    wantDot c, n
  of ParamY, LetY, VarY, ConstY, CursorY, ResultY, FldY:
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

proc semEnumField(c: var SemContext; n: var Cursor; enumType: SymId) =
  let declStart = c.dest.len
  takeToken c, n
  let delayed = handleSymDef(c, n, EfldY) # 0
  let beforeExportMarker = c.dest.len
  wantExportMarker c, n # 1
  var crucial = default CrucialPragma
  semPragmas c, n, crucial, EfldY # 2
  if crucial.magic.len > 0:
    exportMarkerBecomesNifTag c, beforeExportMarker, crucial
  let beforeType = c.dest.len
  if n.kind == DotToken:
    c.dest.add toToken(Symbol, enumType, n.info)
    # no explicit type given:
    inc n # 3
    if n.kind == DotToken:
      # empty value
      takeToken c, n
    else:
      var it = Item(n: n, typ: c.types.autoType)
      semExpr c, it # 4
      n = it.n
      # XXX check that it.typ is an ordinal!
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
  c.addSym delayed
  wantParRi c, n
  publish c, delayed.s.name, declStart

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
  elif n == $InvokeT:
    takeTree c, n
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

proc semProc(c: var SemContext; it: var Item; kind: SymKind; pass: PassKind) =
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
  # 'break' and 'continue' are valid in a template regardless of whether we
  # really have a loop or not:
  if kind == TemplateY:
    inc c.routine.inLoop
    inc c.routine.inGeneric

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
      case pass
      of checkGenericInst:
        if it.n != "stmts":
          error "(stmts) expected, but got ", it.n
        takeToken c, it.n
        semProcBody c, it
        c.closeScope() # close body scope
        c.closeScope() # close parameter scope
      of checkBody:
        if it.n != "stmts":
          error "(stmts) expected, but got ", it.n
        takeToken c, it.n
        let resId = declareResult(c, it.n.info)
        semProcBody c, it
        c.closeScope() # close body scope
        c.closeScope() # close parameter scope
        addReturnResult c, resId, it.n.info
      of checkSignatures:
        c.dest.addDotToken()
        skip it.n
      of checkConceptProc:
        if it.n.kind == DotToken:
          inc it.n
        else:
          c.buildErr it.n.info, "inside a `concept` a routine cannot have a body"
          skip it.n
    else:
      takeToken c, it.n
      c.closeScope() # close parameter scope
  finally:
    c.routine = c.routine.parent
  wantParRi c, it.n
  producesVoid c, info, it.typ
  publish c, symId, declStart

proc semExprSym(c: var SemContext; it: var Item; s: Sym; start: int; flags: set[SemFlag]) =
  it.kind = s.kind
  let expected = it.typ
  if s.kind == NoSym:
    c.buildErr it.n.info, "undeclared identifier"
    it.typ = c.types.autoType
  elif s.kind == CchoiceY:
    if KeepMagics notin flags:
      c.buildErr it.n.info, "ambiguous identifier"
    it.typ = c.types.autoType
  elif s.kind in {TypeY, TypevarY}:
    let typeStart = c.dest.len
    c.dest.buildTree TypedescT, it.n.info:
      c.dest.add toToken(Symbol, s.name, it.n.info)
      semTypeSym c, s, it.n.info, InLocalDecl
    it.typ = typeToCursor(c, typeStart)
    c.dest.shrink typeStart
    commonType c, it, start, expected
  else:
    let res = declToCursor(c, s)
    if KeepMagics notin flags:
      maybeInlineMagic c, res
    if res.status == LacksNothing:
      var n = res.decl
      if s.kind.isLocal or s.kind == EfldY:
        skipToLocalType n
      elif s.kind.isRoutine:
        skipToParams n
      elif s.kind == LabelY:
        discard
      else:
        # XXX enum field?
        assert false, "not implemented"
      it.typ = n
      commonType c, it, start, expected
    else:
      c.buildErr it.n.info, "could not load symbol: " & pool.syms[s.name] & "; errorCode: " & $res.status
      it.typ = c.types.autoType

proc semLocalTypeExpr(c: var SemContext, it: var Item) =
  let val = semLocalType(c, it.n)
  let start = c.dest.len
  c.dest.buildTree TypedescT, it.n.info:
    c.dest.addSubtree val
  it.typ = typeToCursor(c, start)
  c.dest.shrink start

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

proc semStmtBranch(c: var SemContext; it: var Item) =
  # handle statements that could be expressions
  case classifyType(c, it.typ)
  of AutoT:
    semExpr c, it
  of VoidT:
    # performs discard check:
    semStmt c, it.n
  else:
    var ex = Item(n: it.n, typ: it.typ)
    let start = c.dest.len
    semExpr c, ex
    # this is handled by commonType, since it has to be done deeply:
    #if classifyType(c, ex.typ) == VoidT:
    #  # allow statement in expression context if it is noreturn
    #  let ignore = isNoReturn(cursorAt(c.dest, start))
    #  endRead(c.dest)
    #  if not ignore:
    #    typeMismatch(c, it.n.info, ex.typ, it.typ)
    commonType(c, ex, start, it.typ)
    it.n = ex.n

proc semIf(c: var SemContext; it: var Item) =
  let info = it.n.info
  takeToken c, it.n
  if it.n.substructureKind == ElifS:
    while it.n.substructureKind == ElifS:
      takeToken c, it.n
      semBoolExpr c, it.n
      withNewScope c:
        semStmtBranch c, it
      wantParRi c, it.n
  else:
    buildErr c, it.n.info, "illformed AST: `elif` inside `if` expected"
  if it.n.substructureKind == ElseS:
    takeToken c, it.n
    withNewScope c:
      semStmtBranch c, it
    wantParRi c, it.n
  wantParRi c, it.n
  if typeKind(it.typ) == AutoT:
    producesVoid c, info, it.typ

proc isRangeNode(c: var SemContext; n: Cursor): bool =
  var n = n
  if n.exprKind notin {CallX, InfixX}:
    return false
  inc n
  let name = getIdent(c, n)
  result = name != StrId(0) and pool.strings[name] == ".."

proc evalConstIntExpr(c: var SemContext; n: var Cursor; expected: TypeCursor): xint =
  var x = Item(n: n, typ: expected)
  semExpr c, x
  n = x.n
  result = xints.zero()

proc semCaseOfValue(c: var SemContext; it: var Item; selectorType: TypeCursor;
                    seen: var seq[(xint, xint)]) =
  if it.n == "set":
    takeToken c, it.n
    while it.n.kind != ParRi:
      let info = it.n.info
      if isRangeNode(c, it.n):
        inc it.n # call tag
        skip it.n # `..`
        c.dest.buildTree RangeX, it.n.info:
          let a = evalConstIntExpr(c, it.n, selectorType)
          let b = evalConstIntExpr(c, it.n, selectorType)
          if seen.doesOverlapOrIncl(a, b):
            buildErr c, info, "overlapping values"
        inc it.n # right paren of call
      elif it.n.exprKind == RangeX:
        takeToken c, it.n
        let a = evalConstIntExpr(c, it.n, selectorType)
        let b = evalConstIntExpr(c, it.n, selectorType)
        if seen.doesOverlapOrIncl(a, b):
          buildErr c, info, "overlapping values"
        wantParRi c, it.n
      else:
        let a = evalConstIntExpr(c, it.n, selectorType)
        if seen.containsOrIncl(a):
          buildErr c, info, "value already handled"
    wantParRi c, it.n
  else:
    buildErr c, it.n.info, "`set` within `of` expected"
    skip it.n

proc semCase(c: var SemContext; it: var Item) =
  let info = it.n.info
  takeToken c, it.n
  var selector = Item(n: it.n, typ: c.types.autoType)
  semExpr c, selector
  it.n = selector.n
  var seen: seq[(xint, xint)] = @[]
  if it.n.substructureKind == OfS:
    while it.n.substructureKind == OfS:
      takeToken c, it.n
      semCaseOfValue c, it, selector.typ, seen
      withNewScope c:
        semStmtBranch c, it
      wantParRi c, it.n
  else:
    buildErr c, it.n.info, "illformed AST: `of` inside `case` expected"
  if it.n.substructureKind == ElseS:
    takeToken c, it.n
    withNewScope c:
      semStmtBranch c, it
    wantParRi c, it.n
  wantParRi c, it.n
  if typeKind(it.typ) == AutoT:
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
    # `return` within a template refers to the caller, so
    # we allow any type here:
    if c.routine.kind == TemplateY:
      a.typ = c.types.autoType
    semExpr c, a
    it.n = a.n
  wantParRi c, it.n
  producesNoReturn c, info, it.typ

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

  var isGeneric: bool
  if n.kind == DotToken:
    takeToken c, n
    isGeneric = false
  else:
    openScope c
    semGenericParams c, n
    isGeneric = true

  var crucial = default CrucialPragma
  semPragmas c, n, crucial, TypeY # 2
  if crucial.magic.len > 0:
    exportMarkerBecomesNifTag c, beforeExportMarker, crucial

  if n.kind == DotToken:
    takeToken c, n
  else:
    # body
    if n.typeKind == EnumT:
      semEnumType c, n, delayed.s.name
    else:
      semLocalTypeImpl c, n, InTypeSection
  if isGeneric:
    closeScope c
  c.addSym delayed
  wantParRi c, n
  publish c, delayed.s.name, declStart

proc semTypedBinaryArithmetic(c: var SemContext; it: var Item) =
  takeToken c, it.n
  semLocalTypeImpl c, it.n, InLocalDecl
  semExpr c, it
  semExpr c, it
  wantParRi c, it.n

proc semCmp(c: var SemContext; it: var Item) =
  let beforeExpr = c.dest.len
  takeToken c, it.n
  semExpr c, it
  semExpr c, it
  wantParRi c, it.n
  commonType c, it, beforeExpr, c.types.boolType

proc literal(c: var SemContext; it: var Item; literalType: TypeCursor) =
  let beforeExpr = c.dest.len
  takeToken c, it.n
  let expected = it.typ
  it.typ = literalType
  commonType c, it, beforeExpr, expected

proc literalB(c: var SemContext; it: var Item; literalType: TypeCursor) =
  let beforeExpr = c.dest.len
  takeToken c, it.n
  wantParRi c, it.n
  let expected = it.typ
  it.typ = literalType
  commonType c, it, beforeExpr, expected

proc semTypedUnaryArithmetic(c: var SemContext; it: var Item) =
  takeToken c, it.n
  semLocalTypeImpl c, it.n, InLocalDecl
  semExpr c, it
  wantParRi c, it.n

proc semArrayConstr(c: var SemContext, it: var Item) =
  let exprStart = c.dest.len
  takeToken c, it.n
  if it.n.kind == ParRi:
    # empty array
    if it.typ.typeKind in {AutoT, VoidT}:
      buildErr c, it.n.info, "empty array needs a specified type"
    wantParRi c, it.n
    return
  var elem = Item(n: it.n, typ: c.types.autoType)
  case it.typ.typeKind
  of ArrayT: # , SeqT, OpenArrayT
    var arr = it.typ
    inc arr
    elem.typ = arr
  of AutoT: discard
  else:
    buildErr c, it.n.info, "invalid expected type for array constructor: " & typeToString(it.typ)
  # XXX index types, `index: value` etc not implemented
  semExpr c, elem
  var count = 1
  while elem.n.kind != ParRi:
    semExpr c, elem
    inc count
  it.n = elem.n
  wantParRi c, it.n
  let typeStart = c.dest.len
  c.dest.buildTree ArrayT, it.n.info:
    c.dest.addSubtree elem.typ
    c.dest.add toToken(IntLit, pool.integers.getOrIncl(count), it.n.info)
  let expected = it.typ
  it.typ = typeToCursor(c, typeStart)
  c.dest.shrink typeStart
  commonType c, it, exprStart, expected

proc semSetConstr(c: var SemContext, it: var Item) =
  let exprStart = c.dest.len
  takeToken c, it.n
  if it.n.kind == ParRi:
    # empty set
    if it.typ.typeKind in {AutoT, VoidT}:
      buildErr c, it.n.info, "empty set needs a specified type"
    wantParRi c, it.n
    return
  var elem = Item(n: it.n, typ: c.types.autoType)
  case it.typ.typeKind
  of SetT:
    var t = it.typ
    inc t
    elem.typ = t
  of AutoT: discard
  else:
    buildErr c, it.n.info, "invalid expected type for set constructor: " & typeToString(it.typ)
  while elem.n.kind != ParRi:
    if isRangeNode(c, elem.n):
      inc elem.n # call tag
      skip elem.n # `..`
      c.dest.buildTree RangeX, elem.n.info:
        semExpr c, elem
        semExpr c, elem
      inc elem.n # right paren of call
    elif elem.n.exprKind == RangeX:
      skip elem.n # resem elements?
    else:
      semExpr c, elem
    # XXX check if elem.typ is too big
  it.n = elem.n
  wantParRi c, it.n
  let typeStart = c.dest.len
  c.dest.buildTree SetT, it.n.info:
    c.dest.addSubtree elem.typ
  let expected = it.typ
  it.typ = typeToCursor(c, typeStart)
  c.dest.shrink typeStart
  commonType c, it, exprStart, expected

proc semSuf(c: var SemContext, it: var Item) =
  let exprStart = c.dest.len
  takeToken c, it.n
  var num = Item(n: it.n, typ: c.types.autoType)
  semExpr c, num
  it.n = num.n
  if it.n.kind != StringLit:
    c.buildErr it.n.info, "string literal expected for suf"
    skip it.n
    return
  let expected = it.typ
  case pool.strings[it.n.litId]
  of "i": it.typ = c.types.intType
  of "i8": it.typ = c.types.int8Type
  of "i16": it.typ = c.types.int16Type
  of "i32": it.typ = c.types.int32Type
  of "i64": it.typ = c.types.int64Type
  of "u": it.typ = c.types.uintType
  of "u8": it.typ = c.types.uint8Type
  of "u16": it.typ = c.types.uint16Type
  of "u32": it.typ = c.types.uint32Type
  of "u64": it.typ = c.types.uint64Type
  of "f": it.typ = c.types.floatType
  of "f32": it.typ = c.types.float32Type
  of "f64": it.typ = c.types.float64Type
  else:
    c.buildErr it.n.info, "unknown suffix: " & pool.strings[it.n.litId]
  takeToken c, it.n # suffix
  wantParRi c, it.n # right paren
  commonType c, it, exprStart, expected

proc semTupleConstr(c: var SemContext, it: var Item) =
  let exprStart = c.dest.len
  let origExpected = it.typ
  takeToken c, it.n
  if it.n.kind == ParRi:
    wantParRi c, it.n
    it.typ = c.types.emptyTupletype
    commonType c, it, exprStart, origExpected
    return
  var expected = origExpected
  var doExpected = expected.typeKind == TupleT
  if doExpected:
    inc expected # skip tag, now at fields
  let named = it.n.exprKind == KvX
  var typ = createTokenBuf(32)
  typ.add toToken(ParLe, pool.tags.getOrIncl($TupleT), it.n.info)
  var i = 0
  while it.n.kind != ParRi:
    typ.add toToken(ParLe, pool.tags.getOrIncl($FldS), it.n.info) # start field
    if named:
      if it.n.exprKind != KvX:
        c.buildErr it.n.info, "expected field name for named tuple constructor"
      else:
        takeToken c, it.n
        typ.add it.n # add name
        takeToken c, it.n
    else:
      typ.add toToken(Ident, pool.strings.getOrIncl("Field" & $i), it.n.info)
      inc i
    typ.addDotToken() # export marker
    typ.addDotToken() # pragmas
    var elem = Item(n: it.n, typ: c.types.autoType)
    if doExpected:
      let fld = asLocal(expected)
      elem.typ = fld.typ
      skip expected
      if expected.kind == ParRi:
        # happens if expected tuple type has less fields than constructor
        doExpected = false
    semExpr c, elem
    it.n = elem.n
    if named:
      # should be KvX
      wantParRi c, it.n
    typ.addSubtree elem.typ # type
    typ.addDotToken() # value
    typ.addParRi() # end field
  wantParRi c, it.n
  typ.addParRi()
  let typeStart = c.dest.len
  var t = typ.cursorAt(0)
  semTupleType(c, t)
  it.typ = typeToCursor(c, typeStart)
  c.dest.shrink typeStart
  commonType c, it, exprStart, origExpected

proc semDefined(c: var SemContext; it: var Item) =
  inc it.n
  # does not consider dots for now
  let name = pool.strings[getIdent(c, it.n)]
  skipParRi it.n
  let isDefined = name in c.g.config.defines
  let beforeExpr = c.dest.len
  c.dest.addParLe(if isDefined: TrueX else: FalseX, it.n.info)
  c.dest.addParRi()
  let expected = it.typ
  it.typ = c.types.boolType
  commonType c, it, beforeExpr, expected

proc isDeclared(c: var SemContext; name: StrId): bool =
  var scope = c.currentScope
  while scope != nil:
    if name in scope.tab:
      return true
  result = name in c.importTab

proc semDeclared(c: var SemContext; it: var Item) =
  inc it.n
  # does not consider module quoted symbols for now
  let nameId = getIdent(c, it.n)
  skipParRi it.n
  let isDeclared = isDeclared(c, nameId)
  let beforeExpr = c.dest.len
  c.dest.addParLe(if isDeclared: TrueX else: FalseX, it.n.info)
  c.dest.addParRi()
  let expected = it.typ
  it.typ = c.types.boolType
  commonType c, it, beforeExpr, expected

proc semSubscript(c: var SemContext; it: var Item) =
  var n = it.n
  inc n # tag
  var lhsBuf = createTokenBuf(4)
  swap c.dest, lhsBuf
  var lhs = Item(n: n, typ: c.types.autoType)
  semExpr c, lhs, {KeepMagics}
  swap c.dest, lhsBuf
  if lhs.n.kind == Symbol and lhs.kind == TypeY and
      getTypeSection(lhs.n.symId).typevars == "typevars":
    # lhs is a generic type symbol, this is a generic invocation
    # treat it as a type expression to call semInvoke
    semLocalTypeExpr c, it
    return
  # XXX also check for proc generic instantiation, including symchoice

  # build call:
  var callBuf = createTokenBuf(16)
  callBuf.addParLe(CallX, it.n.info)
  callBuf.add toToken(Ident, pool.strings.getOrIncl("[]"), it.n.info)
  callBuf.add lhsBuf
  it.n = lhs.n
  while it.n.kind != ParRi:
    callBuf.takeTree it.n
  callBuf.addParRi()
  skipParRi it.n
  var call = Item(n: cursorAt(callBuf, 0), typ: it.typ)
  semExpr c, call

proc semExpr(c: var SemContext; it: var Item; flags: set[SemFlag] = {}) =
  case it.n.kind
  of IntLit:
    literal c, it, c.types.intType
  of UIntLit:
    literal c, it, c.types.uintType
  of FloatLit:
    literal c, it, c.types.floatType
  of StringLit:
    literal c, it, c.types.stringType
  of CharLit:
    literal c, it, c.types.charType
  of Ident:
    let start = c.dest.len
    let s = semIdent(c, it.n)
    semExprSym c, it, s, start, flags
  of Symbol:
    let start = c.dest.len
    let s = fetchSym(c, it.n.symId)
    takeToken c, it.n
    it.kind = s.kind
    semExprSym c, it, s, start, flags
  of ParLe:
    case exprKind(it.n)
    of QuotedX:
      let start = c.dest.len
      let s = semQuoted(c, it.n)
      it.kind = s.kind
      semExprSym c, it, s, start, flags
    of NoExpr:
      case stmtKind(it.n)
      of NoStmt:
        case typeKind(it.n)
        of NoType, ObjectT, EnumT, DistinctT, ConceptT:
          buildErr c, it.n.info, "expression expected"
        of IntT, FloatT, CharT, BoolT, UIntT, VoidT, StringT, NilT, AutoT, SymKindT,
            PtrT, RefT, MutT, OutT, LentT, SinkT, UncheckedArrayT, SetT, StaticT, TypedescT,
            TupleT, ArrayT, VarargsT, ProcT, IterT:
          # every valid local type expression
          semLocalTypeExpr c, it
        of OrT, AndT, NotT, InvokeT:
          # should be handled in respective expression kinds
          discard
      of ProcS:
        semProc c, it, ProcY, checkBody
      of FuncS:
        semProc c, it, FuncY, checkBody
      of IterS:
        semProc c, it, IterY, checkBody
      of ConverterS:
        semProc c, it, ConverterY, checkBody
      of MethodS:
        semProc c, it, MethodY, checkBody
      of TemplateS:
        semProc c, it, TemplateY, checkBody
      of MacroS:
        semProc c, it, MacroY, checkBody
      of WhileS: semWhile c, it
      of VarS: semLocal c, it, VarY
      of LetS: semLocal c, it, LetY
      of CursorS: semLocal c, it, CursorY
      of ResultS: semLocal c, it, ResultY
      of ConstS: semLocal c, it, ConstY
      of StmtsS: semStmtsExpr c, it
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
      of BlockS:
        semBlock c, it
      of CaseS:
        semCase c, it
      of ForS:
        # XXX
        buildErr c, it.n.info, "statement not implemented"
        skip it.n
    of FalseX, TrueX:
      literalB c, it, c.types.boolType
    of InfX, NegInfX, NanX:
      literalB c, it, c.types.floatType
    of AndX, OrX:
      takeToken c, it.n
      semBoolExpr c, it.n
      semBoolExpr c, it.n
      wantParRi c, it.n
    of NotX:
      c.dest.add it.n
      takeToken c, it.n
      semBoolExpr c, it.n
      wantParRi c, it.n
    of ParX:
      takeToken c, it.n
      semExpr c, it
      wantParRi c, it.n
    of CallX, CmdX, CallStrLitX, InfixX, PrefixX:
      semCall c, it
    of DotX:
      semDot c, it, AlsoTryDotCall
    of EqX, NeqX, LeX, LtX:
      semCmp c, it
    of AshrX, AddX, SubX, MulX, DivX, ModX, ShrX, ShlX, BitandX, BitorX, BitxorX:
      semTypedBinaryArithmetic c, it
    of BitnotX, NegX:
      semTypedUnaryArithmetic c, it
    of AconstrX:
      semArrayConstr c, it
    of SetX:
      semSetConstr c, it
    of SufX:
      semSuf c, it
    of TupleConstrX:
      semTupleConstr c, it
    of DefinedX:
      semDefined c, it
    of DeclaredX:
      semDeclared c, it
    of AtX:
      semSubscript c, it
    of DerefX, PatX, AddrX, NilX, SizeofX, OconstrX, KvX,
       CastX, ConvX, RangeX, RangesX,
       HderefX, HaddrX, OconvX, HconvX, OchoiceX, CchoiceX,
       CompilesX, HighX, LowX, TypeofX, UnpackX:
      # XXX To implement
      takeToken c, it.n
      wantParRi c, it.n

  of ParRi, EofToken, SymbolDef, UnknownToken, DotToken:
    buildErr c, it.n.info, "expression expected"

proc reportErrors(c: var SemContext): int =
  let errTag = pool.tags.getOrIncl("err")
  var i = 0
  var r = Reporter(verbosity: 2, noColors: not useColors())
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

proc semcheck*(infile, outfile: string; config: sink NifConfig; moduleFlags: set[ModuleFlag];
               commandLineArgs: sink string) =
  var n = setupProgram(infile, outfile)
  var c = SemContext(
    dest: createTokenBuf(),
    types: createBuiltinTypes(),
    thisModuleSuffix: prog.main,
    g: ProgramContext(config: config),
    routine: SemRoutine(kind: NoSym),
    commandLineArgs: commandLineArgs)
  c.currentScope = Scope(tab: initTable[StrId, seq[Sym]](), up: nil, kind: ToplevelScope)

  assert n == "stmts"
  takeToken c, n
  while n.kind != ParRi:
    semStmt c, n
  instantiateGenerics c
  for _, val in mpairs(c.instantiatedTypes):
    let s = fetchSym(c, val)
    let res = declToCursor(c, s)
    if res.status == LacksNothing:
      c.dest.copyTree res.decl
  wantParRi c, n
  if reportErrors(c) == 0:
    writeOutput c, outfile
  else:
    quit 1
