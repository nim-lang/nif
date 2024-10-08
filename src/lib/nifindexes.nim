#       Nif library
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Create an index file for a NIF file.

import std / [os, tables, assertions, syncio]
import bitabs, lineinfos, nifreader, nifstreams, nifcursors

proc registerTag(tag: string): TagId = pool.tags.getOrIncl(tag)

proc isImportant(s: string): bool =
  var c = 0
  for ch in s:
    if ch == '.': inc c
  result = c >= 2

proc createIndex*(infile: string) =
  let PublicT = registerTag "public"
  let PrivateT = registerTag "private"
  let KvT = registerTag "kv"

  let indexName = changeFileExt(infile, ".idx.nif")

  var s = nifstreams.open(infile)
  discard processDirectives(s.r)
  var target = -1
  var previousPublicTarget = 0
  var previousPrivateTarget = 0

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
      if pool.syms[sym].isImportant:
        let tb = next(s)
        let isPublic = tb.kind == Ident and pool.strings[tb.litId] == "x"
        var dest =
          if isPublic:
            addr(public)
          else:
            addr(private)
        let diff = if isPublic: target - previousPublicTarget
                  else: target - previousPrivateTarget
        dest[].buildTree KvT, info:
          dest[].add toToken(Symbol, sym, NoLineInfo)
          dest[].add toToken(IntLit, pool.integers.getOrIncl(diff), NoLineInfo)
        if isPublic:
          previousPublicTarget = target
        else:
          previousPrivateTarget = target

  public.addParRi()
  private.addParRi()
  close s

  var outp = open(indexName, fmWrite)
  outp.writeLine "(.nif24)\n(index"
  outp.writeLine toString(public)
  outp.writeLine toString(private)
  outp.writeLine ")"
  close outp

type
  NifIndexEntry* = object
    offset*: int
    info*: PackedLineInfo
  NifIndex* = object
    public*, private*: Table[string, NifIndexEntry]

proc readSection(s: var Stream; tab: var Table[string, NifIndexEntry]) =
  let KvT = registerTag "kv"
  var previousOffset = 0
  var t = next(s)
  var nested = 1
  while t.kind != EofToken:
    let info = t.info
    if t.kind == ParLe:
      inc nested
      if t.tagId == KvT:
        t = next(s)
        var key: string
        if t.kind == Symbol:
          key = pool.syms[t.symId]
        elif t.kind == Ident:
          key = pool.strings[t.litId]
        else:
          assert false, "invalid (kv) construct: symbol expected"
        t = next(s) # skip Symbol
        if t.kind == IntLit:
          let offset = pool.integers[t.intId] + previousOffset
          tab[key] = NifIndexEntry(offset: offset, info: info)
          previousOffset = offset
        else:
          assert false, "invalid (kv) construct: IntLit expected"
        t = next(s) # skip offset
        if t.kind == ParRi:
          t = next(s)
        else:
          assert false, "invalid (kv) construct: IntLit expected"
      else:
        assert false, "expected (kv) construct"
    elif t.kind == ParRi:
      dec nested
      if nested == 0:
        break
      t = next(s)
    else:
      t = next(s)

proc readIndex*(indexName: string): NifIndex =
  var s = nifstreams.open(indexName)
  let res = processDirectives(s.r)
  assert res == Success

  let PublicT = registerTag "public"
  let PrivateT = registerTag "private"
  let IndexT = registerTag "index"

  result = default(NifIndex)
  while true:
    let t = next(s)
    if t.kind == EofToken: break
    if t.kind == ParLe:
      if t.tagId == PublicT:
        readSection s, result.public
      elif t.tagId == PrivateT:
        readSection s, result.private
      elif t.tagId == IndexT:
        discard

when isMainModule:
  createIndex paramStr(1)
