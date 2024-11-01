#
#
#           Gear3 Compiler
#        (c) Copyright 2024 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

import std / [os, tables]

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
    b: Builder

proc load(e: var EContext; suffix: string) =
  if not e.mods.hasKey(suffix):
    let infile = e.dir / suffix & e.ext
    var m = NifModule(stream: nifstreams.open(infile))
    m.buf = fromStream(m.stream)
    e.mods[suffix] = m

proc expand(e: var EContext; c: var Cursor) =
  discard

proc splitModulePath(s: string): (string, string, string) =
  var (dir, main, ext) = splitFile(s)
  let dotPos = find(main, '.')
  if dotPos >= 0:
    ext = substr(main, dotPos) & ext
    main.setLen dotPos
  result = (dir, main, ext)

proc expand*(infile: string) =
  let (dir, file, ext) = splitModulePath(infile)
  var e = EContext(dir: (if dir.len == 0: getCurrentDir() else: dir), ext: ext, main: file)

  var m = NifModule(stream: nifstreams.open(infile))
  m.buf = fromStream(m.stream)
  e.mods[e.main] = m

  var c = beginRead(m.buf)
  expand e, c
  if c.kind != EofToken:
    quit "Internal error: file not processed completely"

when isMainModule:
  echo splitModulePath("/abc/def/name.4.nif")
