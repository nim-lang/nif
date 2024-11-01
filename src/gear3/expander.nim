#
#
#           Gear3 Compiler
#        (c) Copyright 2024 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

import std / [os, tables, syncio, times]

include nifprelude
import nifindexes

type
  NifModule = ref object
    buf: TokenBuf
    stream: Stream
    index: NifIndex
  EContext = object
    mods: Table[string, NifModule]
    dir, main, ext: string
    dest: TokenBuf

proc newNifModule(infile: string): NifModule =
  result = NifModule(stream: nifstreams.open(infile))
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

proc expandOther(e: var EContext; c: var Cursor)

proc expandProc(e: var EContext; c: var Cursor) =
  discard

proc expandOther(e: var EContext; c: var Cursor) =
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

proc expandStmt(e: var EContext; c: var Cursor) =
  var nested = 0
  while true:
    case c.kind
    of EofToken: break
    of ParLe:
      #case c.tag
      #of "proc":
      #  expandProc e, c
      #else:
      #  error e, "unknown statement: ", c
      inc nested
    of ParRi:
      if nested <= 0:
        error e, "unmached ')': ", c
      dec nested
    else:
      error e, "statement expected, but got: ", c
    inc c

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
    dest: createTokenBuf())

  var m = newNifModule(infile)
  var c = beginRead(m.buf)
  e.mods[e.main] = m

  expandStmt e, c
  if c.kind != EofToken:
    quit "Internal error: file not processed completely"

when isMainModule:
  echo splitModulePath("/abc/def/name.4.nif")
