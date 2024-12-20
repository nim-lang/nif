#       Nif library
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Create an index file for a NIF file.

import std / [os, tables, assertions, syncio]
import bitabs, lineinfos, nifreader, nifstreams, nifcursors

import std / [sha1]

proc registerTag(tag: string): TagId = pool.tags.getOrIncl(tag)

proc isImportant(s: string): bool =
  var c = 0
  for ch in s:
    if ch == '.': inc c
  result = c >= 2

proc updateChecksum(dest: var Sha1State; content: TokenBuf) =
  let s = content.toString(false)
  dest.update(s)
  echo "updateChecksum: ", s

type
  IndexChecksum = object
    nested: int
    currentDecl: TokenBuf
    active: int
    remainingKids: int
    needsParRi: bool
    currentConstruct: TagId
    checksum: Sha1State
    letT, varT, cursorT, constT, typeT, procT, templateT, funcT,
      macroT, converterT, methodT, iteratorT, inlineT: TagId

proc initIndexChecksum(): IndexChecksum =
  result = IndexChecksum(
    nested: 0,
    currentDecl: createTokenBuf(60),
    active: -1,
    remainingKids: 0,
    currentConstruct: TagId(0),
    checksum: newSha1State(),
    letT: registerTag("let"),
    varT: registerTag("var"),
    cursorT: registerTag("cursor"),
    constT: registerTag("const"),
    typeT: registerTag("type"),
    procT: registerTag("proc"),
    templateT: registerTag("template"),
    funcT: registerTag("func"),
    macroT: registerTag("macro"),
    converterT: registerTag("converter"),
    methodT: registerTag("method"),
    iteratorT: registerTag("iterator"),
    inlineT: registerTag("inline")
  )

proc handleAtom(b: var IndexChecksum) =
  if b.nested == b.active and b.remainingKids > 0:
    dec b.remainingKids
    if b.remainingKids == 0:
      b.needsParRi = true

proc maybeNewConstruct(b: var IndexChecksum; t: PackedToken) =
  if b.currentConstruct == TagId(0):
    if t.tag in [b.cursorT, b.letT, b.varT, b.constT, b.typeT]:
      b.remainingKids = 5
      b.currentDecl.add t
      b.active = b.nested
      b.currentConstruct = t.tag
      b.needsParRi = false
    elif t.tag in [b.procT, b.funcT, b.macroT, b.converterT, b.methodT]:
      b.remainingKids = 8
      b.currentDecl.add t
      b.active = b.nested
      b.currentConstruct = t.tag
      b.needsParRi = false
    elif t.tag in [b.templateT, b.iteratorT]:
      # these always have inlining semantics:
      b.remainingKids = 9
      b.currentDecl.add t
      b.active = b.nested
      b.currentConstruct = t.tag
      b.needsParRi = false
  elif t.tag == b.inlineT and b.currentConstruct in [b.procT, b.funcT, b.macroT, b.converterT, b.methodT]:
    inc b.remainingKids

proc createIndex*(infile: string; buildChecksum = false) =
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

  var b = initIndexChecksum()
  while true:
    let offs = offset(s.r)
    let t = next(s)
    if t.kind == EofToken: break
    if b.active > 0 and b.remainingKids > 0:
      b.currentDecl.add t
    case t.kind
    of ParLe:
      if b.active == b.nested:
        if b.remainingKids > 0:
          dec b.remainingKids
          if b.remainingKids == 0:
            b.needsParRi = true

      inc b.nested
      if buildChecksum:
        maybeNewConstruct b, t
      target = offs

    of ParRi:
      if b.active == b.nested:
        b.active = -1
        b.currentConstruct = TagId(0)
        b.needsParRi = false

      dec b.nested
    of SymbolDef:
      handleAtom b

      let info = t.info
      let sym = t.symId
      if pool.syms[sym].isImportant:
        let back = offset(s.r)
        let tb = next(s)
        let isPublic = tb.kind != DotToken
        jumpTo s.r, back
        var dest =
          if isPublic:
            addr(public)
          else:
            addr(private)
        let diff = if isPublic: target - previousPublicTarget
                   else: target - previousPrivateTarget
        dest[].buildTree KvT, info:
          dest[].add symToken(sym, NoLineInfo)
          dest[].add intToken(pool.integers.getOrIncl(diff), NoLineInfo)
        if isPublic:
          previousPublicTarget = target
        else:
          previousPrivateTarget = target
    else:
      handleAtom b

    if b.remainingKids == 0:
      if b.currentDecl.len > 0:
        if b.needsParRi:
          b.currentDecl.addParRi()
        updateChecksum(b.checksum, b.currentDecl)
        b.currentDecl.shrink(0)

  public.addParRi()
  private.addParRi()
  close s

  var content = "(.nif24)\n(index\n"
  content.add toString(public)
  content.add "\n"
  content.add toString(private)
  if buildChecksum:
    let final = SecureHash b.checksum.finalize()
    content.add "\n(checksum \"" & $final & "\")"
  content.add "\n)\n"
  if fileExists(indexName) and readFile(indexName) == content:
    discard "no change"
  else:
    writeFile(indexName, content)

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
          raiseAssert "invalid (kv) construct: symbol expected"
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
          dec nested
        else:
          assert false, "invalid (kv) construct: ')' expected"
      else:
        assert false, "expected (kv) construct"
    elif t.kind == ParRi:
      dec nested
      if nested == 0:
        break
      t = next(s)
    else:
      assert false, "expected (kv) construct"
      #t = next(s)

proc readIndex*(indexName: string): NifIndex =
  var s = nifstreams.open(indexName)
  let res = processDirectives(s.r)
  assert res == Success

  let PublicT = registerTag "public"
  let PrivateT = registerTag "private"
  let IndexT = registerTag "index"

  result = default(NifIndex)
  var t = next(s)
  if t.tag == IndexT:
    t = next(s)
    if t.tag == PublicT:
      readSection s, result.public
    else:
      assert false, "'public' expected"
    t = next(s)
    if t.tag == PrivateT:
      readSection s, result.private
    else:
      assert false, "'private' expected"
  else:
    assert false, "expected 'index' tag"

when isMainModule:
  createIndex paramStr(1), true
