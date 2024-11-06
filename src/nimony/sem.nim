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
import nimony_model, symtabs, nifindexes, symparser

type
  NifModule = ref object
    buf: TokenBuf
    stream: Stream
    index: NifIndex

type
  Item* = object
    n, typ: Cursor

  SemRoutine* {.acyclic.} = ref object
    kind: StmtKind
    up: SemRoutine

  SemContext* = object
    r: SemRoutine
    currentScope: Scope
    mods: Table[string, NifModule]
    dir, main, ext: string
    dest: TokenBuf
    mem: seq[seq[PackedToken]]
    nestedIn: seq[(StmtKind, SymId)]

proc newNifModule(infile: string): NifModule =
  result = NifModule(stream: nifstreams.open(infile))
  discard processDirectives(result.stream.r)

  result.buf = fromStream(result.stream)
  let indexName = infile.changeFileExt".idx.nif"
  if not fileExists(indexName) or getLastModificationTime(indexName) < getLastModificationTime(infile):
    createIndex infile
  result.index = readIndex(indexName)

proc load(e: var SemContext; suffix: string): NifModule =
  if not e.mods.hasKey(suffix):
    let infile = e.dir / suffix & e.ext
    result = newNifModule(infile)
    e.mods[suffix] = result
  else:
    result = e.mods[suffix]

proc error(e: var SemContext; msg: string; c: Cursor) =
  write stdout, "[Error] "
  write stdout, msg
  writeLine stdout, toString(c)
  when defined(debug):
    echo getStackTrace()
  quit 1

proc error(e: var SemContext; msg: string) =
  write stdout, "[Error] "
  write stdout, msg
  when defined(debug):
    echo getStackTrace()
  quit 1

proc importSymbol(e: var SemContext; s: SymId): Cursor =
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
    e.mem.add ensureMove(buf)
    result = fromBuffer(e.mem[e.mem.len-1])

proc semStmt(e: var SemContext; c: var Cursor) =
  discard

proc splitModulePath(s: string): (string, string, string) =
  var (dir, main, ext) = splitFile(s)
  let dotPos = find(main, '.')
  if dotPos >= 0:
    ext = substr(main, dotPos) & ext
    main.setLen dotPos
  result = (dir, main, ext)

proc writeOutput(e: var SemContext; outfile: string) =
  var b = nifbuilder.open(outfile)
  b.addHeader "nimony", "nim-sem"
  b.addRaw toString(e.dest)
  b.close()

proc semcheck*(infile, outfile: string) =
  let (dir, file, ext) = splitModulePath(infile)
  var e = SemContext(dir: (if dir.len == 0: getCurrentDir() else: dir), ext: ext, main: file,
    dest: createTokenBuf(),
    nestedIn: @[(StmtsS, SymId(0))])

  var m = newNifModule(infile)
  var c = beginRead(m.buf)
  e.mods[e.main] = m

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

