#
#
#           Gear3 Compiler
#        (c) Copyright 2024 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

import std / [os, tables, sets, syncio, times]

include nifprelude
import nifindexes
import gear3_model

type
  NifModule = ref object
    buf: TokenBuf
    stream: Stream
    index: NifIndex
  EContext = object
    mods: Table[string, NifModule]
    dir, main, ext: string
    dest: TokenBuf
    used, declared: HashSet[SymId]
    nestedIn: seq[StmtKind]
    headers: HashSet[StrId]

proc newNifModule(infile: string): NifModule =
  result = NifModule(stream: nifstreams.open(infile))
  discard processDirectives(result.stream.r)

  result.buf = fromStream(result.stream)
  let indexName = infile.changeFileExt".idx.nif"
  if not fileExists(indexName) or getLastModificationTime(indexName) < getLastModificationTime(infile):
    createIndex infile
  result.index = readIndex(indexName)

proc load(e: var EContext; suffix: string) =
  if not e.mods.hasKey(suffix):
    let infile = e.dir / suffix & e.ext
    e.mods[suffix] = newNifModule(infile)

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

proc traverseExpr(e: var EContext; c: var Cursor)
proc traverseStmt(e: var EContext; c: var Cursor)

proc traverseType(e: var EContext; c: var Cursor) =
  # XXX to implement
  traverseExpr e, c

proc traverseProc(e: var EContext; c: var Cursor) =
  # XXX to implement
  traverseExpr e, c

proc traverseExpr(e: var EContext; c: var Cursor) =
  var nested = 0
  while true:
    case c.kind
    of EofToken: break
    of ParLe:
      e.dest.add c
      inc nested
    of ParRi:
      if nested <= 0:
        error e, "unmached ')': ", c
      e.dest.add c
      dec nested
    of SymbolDef:
      e.dest.add c
    of Symbol:
      e.dest.add c
    of UnknownToken, DotToken, Ident, StringLit, CharLit, IntLit, UIntLit, FloatLit:
      e.dest.add c
    inc c

type
  CollectedPragmas = object
    externName: string
    flags: set[PragmaKind]
    align, bits: IntId
    header: StrId

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
          error e, "unknown pragma: ", c
          inc c
        of ImportC, ImportCpp, ExportC:
          inc c
          expectStrLit e, c
          result.externName = pool.strings[c.litId]
          inc c
        of Nodecl, Selectany, Threadvar, Globalvar, CompileTime:
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

proc traverseLocal(e: var EContext; c: var Cursor; tag: string) =
  let toPatch = e.dest.len
  let vinfo = c.info
  e.add tag, vinfo
  inc c
  expectSymdef(e, c)
  let s = c.symId
  let sinfo = c.info
  inc c
  let pinfo = c.info
  let prag = parsePragmas(e, c)

  var pragmasOpened = false
  if prag.externName.len > 0:
    let nifcName = pool.syms.getOrIncl(prag.externName & ".c")
    e.dest.add toToken(SymbolDef, nifcName, sinfo)
    e.dest.add tagToken("pragmas", pinfo)
    pragmasOpened = true
    e.dest.add tagToken("was", pinfo)
    e.dest.add toToken(Symbol, s, sinfo)
    e.dest.addParRi()
  else:
    e.dest.add toToken(SymbolDef, s, sinfo)

  if Threadvar in prag.flags:
    e.dest[toPatch] = tagToken("tvar", vinfo)
  elif Globalvar in prag.flags:
    e.dest[toPatch] = tagToken("gvar", vinfo)

  if prag.align != IntId(0) or prag.bits != IntId(0):
    if not pragmasOpened:
      e.dest.add tagToken("pragmas", pinfo)
      pragmasOpened = true
    if prag.align != IntId(0):
      e.dest.add tagToken("align", pinfo)
      e.dest.add toToken(IntLit, prag.align, pinfo)
      e.dest.addParRi()
    if prag.bits != IntId(0):
      e.dest.add tagToken("bits", pinfo)
      e.dest.add toToken(IntLit, prag.bits, pinfo)
      e.dest.addParRi()

  if pragmasOpened:
    e.dest.addParRi()
  else:
    e.dest.addDotToken()

  traverseType e, c
  traverseExpr e, c
  wantParRi e, c
  if CompileTime in prag.flags:
    e.dest.shrink toPatch
  elif prag.header != StrId(0):
    e.headers.incl prag.header

proc traverseWhile(e: var EContext; c: var Cursor) =
  e.nestedIn.add WhileS
  e.dest.add c
  inc c
  traverseExpr e, c
  traverseStmt e, c
  wantParRi e, c
  discard e.nestedIn.pop()

proc traverseBlock(e: var EContext; c: var Cursor) =
  e.nestedIn.add BlockS

  discard e.nestedIn.pop()

proc traverseStmt(e: var EContext; c: var Cursor) =
  case c.kind
  of ParLe:
    case c.stmtKind
    of NoStmt:
      error e, "unknown statement: ", c
    of StmtsS:
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
        traverseStmt e, c
    of VarS, LetS, CursorS:
      traverseLocal e, c, (if e.nestedIn[^1] == StmtsS: "gvar" else: "var")
    of ConstS:
      traverseLocal e, c, "const"
    of EmitS, AsgnS, RetS:
      e.dest.add c
      inc c
      while true:
        case c.kind
        of ParRi:
          e.dest.add c
          inc c
          break
        of EofToken:
          error e, "expected ')', but EOF reached"
          break
        else: break
        traverseExpr e, c

    of BreakS: traverseBreak e, c
    of WhileS: traverseWhile e, c
    of BlockS: traverseBlock e, c
    of IfS: traverseIf e, c
    of CaseS: traverseCase e, c
    of YieldS, IterS:
      error e, "to implement: ", c
    of FuncS, ProcS, ConverterS, MethodS:
      traverseProc e, c
    of MacroS, TemplateS:
      # pure compile-time construct, ignore:
      skip c
  else:
    error e, "statement expected, but got: ", c

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
    nestedIn: @[StmtsS])

  var m = newNifModule(infile)
  var c = beginRead(m.buf)
  e.mods[e.main] = m

  traverseStmt e, c
  # fix point expansion:
  #while e.expects.len > 0:
  #  importForeignSymbol()
  if c.kind != EofToken:
    quit "Internal error: file not processed completely"

when isMainModule:
  echo splitModulePath("/abc/def/name.4.nif")
