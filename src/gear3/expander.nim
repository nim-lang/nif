#
#
#           Gear3 Compiler
#        (c) Copyright 2024 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

import std / [hashes, os, tables, sets, syncio, times]

include nifprelude
import nifindexes, symparser
import gear3_model

type
  NifModule = ref object
    buf: TokenBuf
    stream: Stream
    index: NifIndex
  SymbolKey = (SymId, SymId) # (symbol, owner)

  EContext = object
    mods: Table[string, NifModule]
    dir, main, ext: string
    dest: TokenBuf
    declared: HashSet[SymId]
    requires: seq[SymId]
    nestedIn: seq[(StmtKind, SymId)]
    headers: HashSet[StrId]
    currentOwner: SymId
    toMangle: Table[SymbolKey, string]
    nested: int

proc newNifModule(infile: string): NifModule =
  result = NifModule(stream: nifstreams.open(infile))
  discard processDirectives(result.stream.r)

  result.buf = fromStream(result.stream)
  # fromStream only parses the topLevel 'stmts'
  let eof = next(result.stream)
  result.buf.add eof
  let indexName = infile.changeFileExt".idx.nif"
  if not fileExists(indexName) or getLastModificationTime(indexName) < getLastModificationTime(infile):
    createIndex infile
  result.index = readIndex(indexName)

proc load(e: var EContext; suffix: string): NifModule =
  if not e.mods.hasKey(suffix):
    let infile = e.dir / suffix & e.ext
    result = newNifModule(infile)
    e.mods[suffix] = result
  else:
    result = e.mods[suffix]

proc error(e: var EContext; msg: string; c: Cursor) =
  write stdout, "[Error] "
  write stdout, msg
  writeLine stdout, toString(c)
  when defined(debug):
    echo getStackTrace()
  quit 1

proc error(e: var EContext; msg: string) =
  write stdout, "[Error] "
  write stdout, msg
  when defined(debug):
    echo getStackTrace()
  quit 1

proc setOwner(e: var EContext; newOwner: SymId): SymId =
  result = e.currentOwner
  e.currentOwner = newOwner

proc demand(e: var EContext; s: SymId) =
  if not e.declared.contains(s):
    e.requires.add s

proc offer(e: var EContext; s: SymId) =
  e.declared.incl s

proc copyTree(e: var EContext; c: var Cursor) =
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
        error e, "expected ')', but EOF reached"
        break
      else: discard
      inc c

proc wantParRi(e: var EContext; c: var Cursor) =
  if c.kind == ParRi:
    e.dest.add c
    inc c
  else:
    error e, "expected ')', but got: ", c

proc skipParRi(e: var EContext; c: var Cursor) =
  if c.kind == ParRi:
    inc c
  else:
    error e, "expected ')', but got: ", c

proc skipExportMarker(e: var EContext; c: var Cursor) =
  if c.kind == DotToken:
    inc c
  elif c.kind == Ident and pool.strings[c.litId] == "x":
    inc c
  else:
    error e, "expected '.' or 'x' for an export marker: ", c

proc expectSymdef(e: var EContext; c: var Cursor) =
  if c.kind != SymbolDef:
    error e, "expected symbol definition, but got: ", c

proc expectSym(e: var EContext; c: var Cursor) =
  if c.kind != Symbol:
    error e, "expected symbol, but got: ", c

proc expectStrLit(e: var EContext; c: var Cursor) =
  if c.kind != StringLit:
    error e, "expected string literal, but got: ", c

proc expectIntLit(e: var EContext; c: var Cursor) =
  if c.kind != IntLit:
    error e, "expected int literal, but got: ", c

proc tagToken(tag: string; info: PackedLineInfo): PackedToken {.inline.} =
  toToken(ParLe, pool.tags.getOrIncl(tag), info)

proc add(e: var EContext; tag: string; info: PackedLineInfo) =
  e.dest.add tagToken(tag, info)

type
  TraverseMode = enum
    TraverseAll, TraverseSig, TraverseTopLevel

proc traverseExpr(e: var EContext; c: var Cursor)
proc traverseStmt(e: var EContext; c: var Cursor; mode = TraverseAll)
proc traverseLocal(e: var EContext; c: var Cursor; tag: string; mode: TraverseMode)

template loop(e: var EContext; c: var Cursor; body: untyped) =
  while true:
    case c.kind
    of ParRi:
      e.dest.add c
      inc c
      break
    of EofToken:
      error e, "expected ')', but EOF reached"
      break
    else: discard
    body

type
  TypeFlag = enum
    IsTypeBody
    IsPointerOf

proc traverseType(e: var EContext; c: var Cursor; flags: set[TypeFlag] = {}) =
  case c.kind
  of DotToken:
    e.dest.add c
    inc c
  of Symbol:
    e.demand c.symId
    e.dest.add c
    inc c
  of ParLe:
    case c.typeKind
    of NoType, OrT, AndT, NotT:
      error e, "type expected but got: ", c
    of IntT, UIntT, FloatT, CharT, BoolT, AutoT, SymKindT:
      e.loop c:
        e.dest.add c
        inc c
    of PtrT, RefT, MutT, OutT, LentT:
      e.dest.add tagToken("ptr", c.info)
      inc c
      e.loop c:
        traverseType e, c, {IsPointerOf}
    of ProcT:
      e.dest.add c
      inc c
      e.loop c:
        traverseType e, c
    of ArrayT:
      e.dest.add c
      inc c
      traverseType e, c
      traverseExpr e, c
      wantParRi e, c
    of UncheckedArrayT:
      if IsPointerOf in flags:
        inc c
        traverseType e, c
        skipParRi e, c
      else:
        e.dest.add tagToken("flexarray", c.info)
        inc c
        traverseType e, c
        wantParRi e, c
    of StaticT, SinkT, DistinctT:
      inc c
      traverseType e, c, flags
      skipParRi e, c
    of ObjectT, TupleT, EnumT, VoidT, StringT, VarargsT, NilT, ConceptT,
       IterT, InvokeT, SetT:
      error e, "unimplemented type: ", c
  else:
    error e, "type expected but got: ", c

proc traverseParams(e: var EContext; c: var Cursor) =
  traverseType e, c
  if c.kind == DotToken:
    e.dest.add c
    inc c
  elif c.kind == ParLe and pool.tags[c.tag] == $ParamsS:
    e.dest.add c
    inc c
    loop e, c:
      if c.substructureKind != ParamS:
        error e, "expected (param) but got: ", c
      traverseLocal(e, c, "param", TraverseSig)

type
  CollectedPragmas = object
    externName: string
    flags: set[PragmaKind]
    align, bits: IntId
    header: StrId
    callConv: CallConv

proc parsePragmas(e: var EContext; c: var Cursor): CollectedPragmas =
  result = default(CollectedPragmas)
  if c.kind == DotToken:
    inc c
  elif c.kind == ParLe and pool.tags[c.tag] == $PragmasS:
    inc c
    while true:
      case c.kind
      of ParRi:
        inc c
        break
      of EofToken:
        error e, "expected ')', but EOF reached"
        break
      else: discard
      if c.kind == ParLe:
        let pk = c.pragmaKind
        case pk
        of NoPragma:
          let cc = c.callConvKind
          if cc == NoCallConv:
            error e, "unknown pragma: ", c
          else:
            result.callConv = cc
          inc c
        of ImportC, ImportCpp, ExportC:
          inc c
          expectStrLit e, c
          result.externName = pool.strings[c.litId]
          inc c
        of Nodecl, Selectany, Threadvar, Globalvar:
          result.flags.incl pk
          inc c
        of Header:
          inc c
          expectStrLit e, c
          result.header = c.litId
          inc c
        of Align:
          inc c
          expectIntLit e, c
          result.align = c.intId
          inc c
        of Bits:
          inc c
          expectIntLit e, c
          result.bits = c.intId
          inc c
        skipParRi e, c
      else:
        error e, "unknown pragma: ", c
  else:
    error e, "(pragmas) or '.' expected, but got: ", c

type
  GenPragmas = object
    opened: bool

proc openGenPragmas(): GenPragmas = GenPragmas(opened: false)

proc maybeOpen(e: var EContext; g: var GenPragmas; info: PackedLineInfo) {.inline.} =
  if not g.opened:
    g.opened = true
    e.dest.add tagToken("pragmas", info)

proc addKey(e: var EContext; g: var GenPragmas; key: string; info: PackedLineInfo) =
  maybeOpen e, g, info
  e.dest.add tagToken(key, info)
  e.dest.addParRi()

proc addKeyVal(e: var EContext; g: var GenPragmas; key: string; val: PackedToken; info: PackedLineInfo) =
  maybeOpen e, g, info
  e.dest.add tagToken(key, info)
  e.dest.add val
  e.dest.addParRi()

proc closeGenPragmas(e: var EContext; g: GenPragmas) =
  if g.opened:
    e.dest.addParRi()
  else:
    e.dest.addDotToken()

proc traverseProc(e: var EContext; c: var Cursor; mode: TraverseMode) =
  # patternPos* = 1    # empty except for term rewriting macros
  # genericParamsPos* = 2
  # paramsPos* = 3
  # pragmasPos* = 4
  # miscPos* = 5  # used for undocumented and hacky stuff
  # bodyPos* = 6       # position of body; use rodread.getBody() instead!
  var dst = createTokenBuf(50)
  swap e.dest, dst
  #let toPatch = e.dest.len
  let vinfo = c.info
  e.add "proc", vinfo
  inc c
  expectSymdef(e, c)
  let s = c.symId
  let sinfo = c.info
  inc c
  skipExportMarker e, c
  skip c # patterns
  let isGeneric = c.kind != DotToken
  skip c # generic parameters
  traverseParams e, c
  let pinfo = c.info
  let prag = parsePragmas(e, c)

  e.dest.add toToken(SymbolDef, s, sinfo)
  e.offer s
  let oldOwner = setOwner(e, s)

  var genPragmas = openGenPragmas()
  if prag.externName.len > 0:
    e.toMangle[(s, oldOwner)] = prag.externName & ".c"
    e.addKeyVal genPragmas, "was", toToken(Symbol, s, pinfo), pinfo
  if Selectany in prag.flags:
    e.addKey genPragmas, "selectany", pinfo
  closeGenPragmas e, genPragmas

  # body:
  if mode != TraverseSig or prag.callConv == InlineC:
    traverseStmt e, c, TraverseAll
  else:
    skip c
  wantParRi e, c
  swap dst, e.dest
  if Nodecl in prag.flags or isGeneric:
    discard "do not add to e.dest"
  else:
    e.dest.add dst
  if prag.header != StrId(0):
    e.headers.incl prag.header
  discard setOwner(e, oldOwner)

proc traverseTypeDecl(e: var EContext; c: var Cursor) =
  var dst = createTokenBuf(50)
  swap e.dest, dst
  #let toPatch = e.dest.len
  let vinfo = c.info
  e.add "type", vinfo
  inc c
  expectSymdef(e, c)
  let s = c.symId
  let sinfo = c.info
  let oldOwner = setOwner(e, s)
  inc c
  skipExportMarker e, c
  let isGeneric = c.kind != DotToken
  skip c # generic parameters

  let pinfo = c.info
  let prag = parsePragmas(e, c)
  traverseType e, c, {IsTypeBody}
  wantParRi e, c
  swap dst, e.dest
  if Nodecl in prag.flags or isGeneric:
    discard "do not add to e.dest"
  else:
    e.dest.add dst
  if prag.header != StrId(0):
    e.headers.incl prag.header
  discard setOwner(e, oldOwner)

proc traverseExpr(e: var EContext; c: var Cursor) =
  while true:
    case c.kind
    of EofToken: break
    of ParLe:
      e.dest.add c
      inc e.nested
    of ParRi:
      if e.nested <= 0:
        inc c
        if c.kind == EofToken:
          unsafeDec(c)
          break
        else:
          unsafeDec(c)
          error e, "unmached ')': ", c
      else:
        e.dest.add c
        dec e.nested
    of SymbolDef:
      e.dest.add c
      e.offer c.symId
    of Symbol:
      e.dest.add c
      e.demand c.symId
    of UnknownToken, DotToken, Ident, StringLit, CharLit, IntLit, UIntLit, FloatLit:
      e.dest.add c
    inc c

proc traverseLocal(e: var EContext; c: var Cursor; tag: string; mode: TraverseMode) =
  let toPatch = e.dest.len
  let vinfo = c.info
  e.add tag, vinfo
  inc c
  expectSymdef(e, c)
  let s = c.symId
  let sinfo = c.info
  inc c
  skipExportMarker e, c
  let pinfo = c.info
  let prag = parsePragmas(e, c)

  e.dest.add toToken(SymbolDef, s, sinfo)
  e.offer s

  var genPragmas = openGenPragmas()

  if prag.externName.len > 0:
    e.toMangle[(s, e.currentOwner)] = prag.externName & ".c"
    e.addKeyVal genPragmas, "was", toToken(Symbol, s, pinfo), pinfo

  if Threadvar in prag.flags:
    e.dest[toPatch] = tagToken("tvar", vinfo)
  elif Globalvar in prag.flags:
    e.dest[toPatch] = tagToken("gvar", vinfo)

  if prag.align != IntId(0):
    e.addKeyVal genPragmas, "align", toToken(IntLit, prag.align, pinfo), pinfo
  if prag.bits != IntId(0):
    e.addKeyVal genPragmas, "bits", toToken(IntLit, prag.bits, pinfo), pinfo
  closeGenPragmas e, genPragmas

  traverseType e, c
  if mode != TraverseSig:
    traverseExpr e, c
  else:
    skip c
  # wantParRi e, c
  if Nodecl in prag.flags:
    e.dest.shrink toPatch
  if prag.header != StrId(0):
    e.headers.incl prag.header

proc traverseWhile(e: var EContext; c: var Cursor) =
  let info = c.info
  e.nestedIn.add (WhileS, SymId(0))
  e.dest.add c
  inc c
  traverseExpr e, c
  traverseStmt e, c
  wantParRi e, c
  let lab = e.nestedIn[^1][1]
  if lab != SymId(0):
    e.dest.add tagToken("lab", info)
    e.dest.add toToken(SymbolDef, lab, info)
    e.offer lab
    e.dest.addParRi()
  discard e.nestedIn.pop()

proc traverseBlock(e: var EContext; c: var Cursor) =
  let info = c.info
  inc c
  if c.kind == DotToken:
    e.nestedIn.add (BlockS, SymId(0))
    inc c
  else:
    expectSymdef e, c
    e.nestedIn.add (BlockS, c.symId)
    inc c
  e.dest.add tagToken("scope", info)
  traverseStmt e, c
  wantParRi e, c
  let lab = e.nestedIn[^1][1]
  if lab != SymId(0):
    e.dest.add tagToken("lab", info)
    e.dest.add toToken(SymbolDef, lab, info)
    e.offer lab
    e.dest.addParRi()
  discard e.nestedIn.pop()

proc traverseBreak(e: var EContext; c: var Cursor) =
  let info = c.info
  inc c
  if c.kind == DotToken:
    inc c
    e.dest.add tagToken("break", info)
  else:
    expectSym e, c
    let lab = c.symId
    inc c
    e.dest.add tagToken("jmp", info)
    e.dest.add toToken(Symbol, lab, info)
  wantParRi e, c

proc traverseIf(e: var EContext; c: var Cursor) =
  # (if cond (.. then ..) (.. else ..))
  e.dest.add c
  inc c
  traverseExpr e, c
  traverseStmt e, c
  traverseStmt e, c
  wantParRi e, c

proc traverseCase(e: var EContext; c: var Cursor) =
  e.dest.add c
  inc c
  traverseExpr e, c
  while c.kind != ParRi:
    case c.substructureKind
    of OfS:
      e.dest.add c
      inc c
      traverseExpr e, c
      traverseStmt e, c
      wantParRi e, c
    of ElseS:
      e.dest.add c
      inc c
      traverseStmt e, c
      wantParRi e, c
    else:
      error e, "expected (of) or (else) but got: ", c
  traverseStmt e, c
  wantParRi e, c

proc traverseStmt(e: var EContext; c: var Cursor; mode = TraverseAll) =
  case c.kind
  of DotToken:
    e.dest.add c
    inc c
  of ParLe:
    case c.stmtKind
    of NoStmt:
      error e, "unknown statement: ", c
    of StmtsS:
      if mode == TraverseTopLevel:
        inc c
        while c.kind notin {EofToken, ParRi}:
          traverseStmt e, c, mode
        skipParRi e, c
      else:
        e.dest.add c
        inc c
        e.loop c:
          traverseStmt e, c, mode
    of VarS, LetS, CursorS:
      inc e.nested
      traverseLocal e, c, (if e.nestedIn[^1][0] == StmtsS: "gvar" else: "var"), mode
      dec e.nested
    of ConstS:
      inc e.nested
      traverseLocal e, c, "const", mode
      dec e.nested
    of EmitS, AsgnS, RetS:
      e.dest.add c
      inc c
      e.loop c:
        traverseExpr e, c

    of BreakS: traverseBreak e, c
    of WhileS: traverseWhile e, c
    of BlockS: traverseBlock e, c
    of IfS: traverseIf e, c
    of CaseS: traverseCase e, c
    of YieldS, IterS:
      error e, "to implement: ", c
    of FuncS, ProcS, ConverterS, MethodS:
      traverseProc e, c, mode
    of MacroS, TemplateS:
      # pure compile-time construct, ignore:
      skip c
    of TypeS:
      traverseTypeDecl e, c
  else:
    error e, "statement expected, but got: ", c

proc importSymbol(e: var EContext; s: SymId) =
  let nifName = pool.syms[s]
  let modname = extractModule(nifName)
  if modname == "":
    error e, "undeclared identifier: " & nifName
  else:
    var m = load(e, modname)
    var entry = m.index.public.getOrDefault(nifName)
    if entry.offset == 0:
      entry = m.index.private.getOrDefault(nifName)
    if entry.offset == 0:
      error e, "undeclared identifier: " & nifName
    m.stream.r.jumpTo entry.offset
    var buf: seq[PackedToken] = @[]
    discard nifstreams.parse(m.stream.r, buf, entry.info)
    var c = fromBuffer(buf)
    e.dest.add tagToken("imp", c.info)
    traverseStmt e, c, TraverseSig
    e.dest.addParRi()

proc writeOutput(e: var EContext) =
  var b = nifbuilder.open(e.dir / e.main & ".c.nif")
  b.addHeader "gear3", "nifc"
  b.addTree "stmts"
  for h in e.headers:
    b.withTree "incl":
      b.addStrLit pool.strings[h]

  var c = beginRead(e.dest)
  var ownerStack = @[(SymId(0), -1)]

  var stack: seq[PackedLineInfo] = @[]
  var nested = 0
  var nextIsOwner = -1
  for n in 0 ..< e.dest.len:
    let info = c.info
    if info.isValid:
      var (file, line, col) = unpack(pool.man, info)
      var fileAsStr = ""
      if stack.len > 0:
        let (pfile, pline, pcol) = unpack(pool.man, stack[^1])
        line = line - pline
        col = col - pcol
        if file != pfile: fileAsStr = pool.files[file]
      b.addLineInfo(col, line, fileAsStr)

    case c.kind
    of DotToken:
      b.addEmpty()
    of Ident:
      b.addIdent(pool.strings[c.litId])
    of Symbol:
      let owner = ownerStack[^1][0]
      let key = (c.symId, owner)
      let val = e.toMangle.getOrDefault(key)
      if val.len > 0:
        b.addSymbol(val)
      else:
        b.addSymbol(pool.syms[c.symId])
    of IntLit:
      b.addIntLit(pool.integers[c.intId])
    of UIntLit:
      b.addUIntLit(pool.uintegers[c.uintId])
    of FloatLit:
      b.addFloatLit(pool.floats[c.floatId])
    of SymbolDef:
      let owner = ownerStack[^1][0]
      let key = (c.symId, owner)
      let val = e.toMangle.getOrDefault(key)
      if val.len > 0:
        b.addSymbolDef(val)
      else:
        b.addSymbolDef(pool.syms[c.symId])
      if nextIsOwner >= 0:
        ownerStack.add (c.symId, nextIsOwner)
        nextIsOwner = -1
    of CharLit:
      b.addCharLit char(c.uoperand)
    of StringLit:
      b.addStrLit(pool.strings[c.litId])
    of UnknownToken:
      b.addIdent "<unknown token>"
    of EofToken:
      b.addIntLit c.soperand
    of ParRi:
      discard stack.pop()
      b.endTree()
      if nested > 0: dec nested
      if ownerStack[^1][1] == nested:
        discard ownerStack.pop()
    of ParLe:
      let tag = pool.tags[c.tagId]
      if tag == "proc" or tag == "type":
        nextIsOwner = nested
      b.addTree(tag)
      stack.add info
      inc nested
    inc c

  b.endTree()
  b.close()

proc splitModulePath(s: string): (string, string, string) =
  var (dir, main, ext) = splitFile(s)
  let dotPos = find(main, '.')
  if dotPos >= 0:
    ext = substr(main, dotPos) & ext
    main.setLen dotPos
  result = (dir, main, ext)

proc expand*(infile: string) =
  let (dir, file, ext) = splitModulePath(infile)
  var e = EContext(dir: (if dir.len == 0: getCurrentDir() else: dir), ext: ext, main: file,
    dest: createTokenBuf(),
    nestedIn: @[(StmtsS, SymId(0))])

  var m = newNifModule(infile)
  var c = beginRead(m.buf)
  e.mods[e.main] = m

  traverseStmt e, c, TraverseTopLevel
  if c.kind != EofToken:
    quit "Internal error: file not processed completely"
  # fix point expansion:
  var i = 0
  while i < e.requires.len:
    let imp = e.requires[i]
    if not e.declared.contains(imp):
      importSymbol(e, imp)
    inc i
  writeOutput e

when isMainModule:
  echo splitModulePath("/abc/def/name.4.nif")
