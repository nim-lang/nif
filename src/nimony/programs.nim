#       Nimony
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

import std / [syncio, os, tables, times]
include nifprelude
import nifindexes, symparser

type
  NifModule = ref object
    buf: TokenBuf
    stream: Stream
    index: NifIndex

  Program* = object
    mods: Table[string, NifModule]
    dir, main, ext: string
    mem: seq[seq[PackedToken]]

var
  prog: Program

proc newNifModule(infile: string): NifModule =
  result = NifModule(stream: nifstreams.open(infile))
  discard processDirectives(result.stream.r)

  result.buf = fromStream(result.stream)
  let indexName = infile.changeFileExt".idx.nif"
  if not fileExists(indexName) or getLastModificationTime(indexName) < getLastModificationTime(infile):
    createIndex infile
  result.index = readIndex(indexName)

proc load*(suffix: string): NifModule =
  if not prog.mods.hasKey(suffix):
    let infile = prog.dir / suffix & prog.ext
    result = newNifModule(infile)
    prog.mods[suffix] = result
  else:
    result = prog.mods[suffix]

proc error*(msg: string; c: Cursor) =
  write stdout, "[Error] "
  write stdout, msg
  writeLine stdout, toString(c)
  when defined(debug):
    echo getStackTrace()
  quit 1

proc error*(msg: string) =
  write stdout, "[Error] "
  write stdout, msg
  when defined(debug):
    echo getStackTrace()
  quit 1

proc importSymbol*(s: SymId): Cursor =
  let nifName = pool.syms[s]
  let modname = extractModule(nifName)
  if modname == "":
    error "undeclared identifier: " & nifName
  else:
    var m = load(modname)
    var entry = m.index.public.getOrDefault(nifName)
    if entry.offset == 0:
      entry = m.index.private.getOrDefault(nifName)
    if entry.offset == 0:
      error "undeclared identifier: " & nifName
    m.stream.r.jumpTo entry.offset
    var buf: seq[PackedToken] = @[]
    discard nifstreams.parse(m.stream.r, buf, entry.info)
    prog.mem.add ensureMove(buf)
    result = fromBuffer(prog.mem[prog.mem.len-1])

proc loadSym*(s: SymId): Cursor =
  result = importSymbol(s)

proc splitModulePath(s: string): (string, string, string) =
  var (dir, main, ext) = splitFile(s)
  let dotPos = find(main, '.')
  if dotPos >= 0:
    ext = substr(main, dotPos) & ext
    main.setLen dotPos
  result = (dir, main, ext)

proc setupProgram*(infile: string): Cursor =
  let (dir, file, ext) = splitModulePath(infile)
  prog.dir = (if dir.len == 0: getCurrentDir() else: dir)
  prog.ext = ext
  prog.main = file

  var m = newNifModule(infile)
  result = beginRead(m.buf)
  prog.mods[prog.main] = m
