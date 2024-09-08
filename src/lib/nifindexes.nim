#       Nif library
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Create an index file for a NIF file.

import std / [os]
import bitabs, lineinfos, nifreader, nifstreams, nifcursors

proc registerTag(tag: string): TagId = pool.tags.getOrIncl(tag)

proc createIndex*(infile: string) =
  let PublicT = registerTag "public"
  let PrivateT = registerTag "private"
  let KvT = registerTag "kv"

  let indexName = changeFileExt(infile, ".idx.nif")

  var s = nifstreams.open(infile)
  discard processDirectives(s.r)
  var target = -1
  var previousTarget = 0

  var public = default(TokenBuf)
  var private = default(TokenBuf)
  public.addParLe PublicT
  private.addParLe PrivateT

  while true:
    let offs = offset(s.r)
    let t = next(s)
    if t.kind == EofToken: break
    if t.kind == ParLe:
      target = offs
    elif t.kind == SymbolDef:
      let info = t.info
      let sym = t.symId
      let tb = next(s)
      var dest =
        if tb.kind == Ident and pool.strings[tb.litId] == "x":
          addr(public)
        else:
          addr(private)
      dest[].buildTree KvT, info:
        dest[].add toToken(Symbol, sym, NoLineInfo)
        dest[].add toToken(IntLit, pool.integers.getOrIncl(target - previousTarget), NoLineInfo)
      previousTarget = target

  public.addParRi()
  private.addParRi()
  close s

  var outp = open(indexName, fmWrite)
  outp.writeLine "(.nif24)\n(index"
  outp.writeLine toString(public)
  outp.writeLine toString(private)
  outp.writeLine ")"
  close outp

when isMainModule:
  createIndex paramStr(1)
