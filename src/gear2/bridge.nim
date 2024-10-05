#       Nifler
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Implements the mapping from Nim sem's AST to NIF ("gear2").

when defined(nifBench):
  import std / monotimes

import std / [strutils]

import "$nim" / compiler / [
  ast, options, pathutils, renderer, lineinfos,
  parser, llstream, idents, msgs]

import ".." / lib / [nifbuilder, nifindexes]
import modnames, enum2nif

type
  WContext = object # writer context
    conf: ConfigRef
    section: string
    b: Builder

proc absLineInfo(i: TLineInfo; c: var WContext) =
  c.b.addLineInfo int32(i.col), int32(i.line), toFullPath(c.conf, i.fileIndex)

proc relLineInfo(n, parent: PNode; c: var WContext;
                 emitSpace = false) =
  let i = n.info
  if parent == nil:
    absLineInfo i, c
    return
  let p = parent.info
  if i.fileIndex != p.fileIndex:
    absLineInfo i, c
    return

  let colDiff = int32(i.col) - int32(p.col)
  let lineDiff = int32(i.line) - int32(p.line)
  c.b.addLineInfo colDiff, lineDiff, ""

proc symToNif(s: PSym; c: var WContext; isDef = false) =
  var m = s.name.s & '.' & $s.disamb
  if s.skipGenericOwner().kind == skModule:
    m.add '.'
    m.add moduleSuffix(toFullPath(c.conf, s.info.fileIndex))
  if isDef:
    c.b.addSymbolDef m
  else:
    c.b.addSymbol m

proc toNif*(n, parent: PNode; c: var WContext)
proc toNif*(t: PType; parent: PNode; c: var WContext)

proc symToNif(n: PNode; parent: PNode; c: var WContext; isDef = false) =
  if not isDef and n.typ != n.sym.typ:
    c.b.withTree "htype":
      toNif n.typ, parent, c
      symToNif n.sym, c, isDef
  else:
    symToNif n.sym, c, isDef

include typebridge

proc toNifDecl(n, parent: PNode; c: var WContext) =
  if n.kind == nkSym:
    relLineInfo(n, parent, c)
    symToNif(n, parent, c, true)
  else:
    toNif n, parent, c

proc magicCall(m: TMagic; n: PNode; c: var WContext) =
  c.b.addTree(toNifTag(m))
  for i in 1..<n.len:
    toNif(n[i], n, c)
  c.b.endTree

proc writeFlags[E](b: var Builder; flags: set[E]) =
  var flagsAsIdent = ""
  genFlags(flags, flagsAsIdent)
  if flagsAsIdent.len > 0:
    b.addIdent flagsAsIdent

proc writeNodeFlags(b: var Builder; flags: set[TNodeFlag]) {.inline.} =
  # we know nodes can have been sem'checked:
  writeFlags b, flags - {nfSem}

proc toNifPragmas(n, name, parent: PNode; c: var WContext) =
  var b2 = nifbuilder.open(30)
  b2.withTree "pragmas":
    if name.kind == nkSym:
      let flags = name.sym.flags
      if sfImportc in flags:
        b2.withTree "importc":
          b2.addIdent name.sym.loc.snippet
      elif sfExportc in flags:
        b2.withTree "exportc":
          b2.addIdent name.sym.loc.snippet
      b2.writeFlags flags - {sfImportc, sfExportc}
    elif n != nil:
      for ch in n:
        toNif ch, n, c
  let s = b2.extract()
  if s.len > len("(pragmas)"):
    c.b.addRaw s
  else:
    c.b.addEmpty

proc addIntLit(b: var Builder; i: BiggestInt; suffix: string) =
  b.withTree "suf":
    b.addIntLit i
    b.addStrLit suffix

proc addFloatLit(b: var Builder; i: BiggestFloat; suffix: string) =
  b.withTree "suf":
    b.addFloatLit i
    b.addStrLit suffix

proc toNif*(n, parent: PNode; c: var WContext) =
  case n.kind
  of nkNone, nkEmpty:
    c.b.addEmpty 1
  of nkSym:
    relLineInfo(n, parent, c)
    symToNif(n, parent, c)
  of nkCommand, nkCall, nkCallStrLit, nkInfix, nkPrefix, nkPostfix, nkHiddenCallConv:
    relLineInfo(n, parent, c)
    if n.len > 0 and n[0].kind == nkSym and n[0].sym.magic != mNone:
      magicCall n[0].sym.magic, n, c
    else:
      c.b.addTree(toNifTag(n.kind))
      c.b.writeNodeFlags n.flags
      for i in 0..<n.len:
        toNif(n[i], n, c)
      c.b.endTree
  of nkNilLit:
    relLineInfo(n, parent, c)
    c.b.addKeyw "nil"
  of nkStrLit:
    relLineInfo(n, parent, c)
    c.b.addStrLit n.strVal, ""
  of nkRStrLit:
    relLineInfo(n, parent, c)
    c.b.addStrLit n.strVal, "R"
  of nkTripleStrLit:
    relLineInfo(n, parent, c)
    c.b.addStrLit n.strVal, "T"
  of nkCharLit:
    relLineInfo(n, parent, c)
    c.b.addCharLit char(n.intVal)
  of nkIntLit:
    relLineInfo(n, parent, c, true)
    c.b.addIntLit n.intVal
  of nkInt8Lit:
    relLineInfo(n, parent, c, true)
    c.b.addIntLit n.intVal, "i8"
  of nkInt16Lit:
    relLineInfo(n, parent, c, true)
    c.b.addIntLit n.intVal, "i16"
  of nkInt32Lit:
    relLineInfo(n, parent, c, true)
    c.b.addIntLit n.intVal, "i32"
  of nkInt64Lit:
    relLineInfo(n, parent, c, true)
    c.b.addIntLit n.intVal, "i64"
  of nkUIntLit:
    relLineInfo(n, parent, c, true)
    c.b.addUIntLit cast[BiggestUInt](n.intVal)
  of nkUInt8Lit:
    relLineInfo(n, parent, c, true)
    c.b.addUIntLit cast[BiggestUInt](n.intVal), "u8"
  of nkUInt16Lit:
    relLineInfo(n, parent, c, true)
    c.b.addUIntLit cast[BiggestUInt](n.intVal), "u16"
  of nkUInt32Lit:
    relLineInfo(n, parent, c, true)
    c.b.addUIntLit cast[BiggestUInt](n.intVal), "u32"
  of nkUInt64Lit:
    relLineInfo(n, parent, c, true)
    c.b.addUIntLit cast[BiggestUInt](n.intVal), "u64"
  of nkFloatLit:
    relLineInfo(n, parent, c, true)
    c.b.addFloatLit n.floatVal
  of nkFloat32Lit:
    relLineInfo(n, parent, c, true)
    c.b.addFloatLit n.floatVal, "f32"
  of nkFloat64Lit:
    relLineInfo(n, parent, c, true)
    c.b.addFloatLit n.floatVal, "f64"
  of nkFloat128Lit:
    relLineInfo(n, parent, c, true)
    c.b.addFloatLit n.floatVal, "f128"
  of nkIdent:
    relLineInfo(n, parent, c, true)
    c.b.addIdent n.ident.s
  of nkTypeDef:
    relLineInfo(n, parent, c)
    c.b.addTree("type")
    var name: PNode
    var visibility: PNode
    var pragma: PNode
    if n[0].kind == nkPragmaExpr:
      pragma = n[0][1]
      if n[0][0].kind == nkPostfix:
        visibility = n[0][0][0]
        name = n[0][0][1]
      else:
        name = n[0][0]
    elif n[0].kind == nkPostfix:
      visibility = n[0][0]
      name = n[0][1]
    else:
      name = n[0]

    toNifDecl(name, n, c)

    if visibility != nil:
      c.b.addIdent "x"
    else:
      c.b.addEmpty

    toNifPragmas(pragma, name, n, c)

    for i in 1..<n.len:
      toNif(n[i], n, c)
    c.b.endTree

  of nkTypeSection:
    for i in 0..<n.len:
      toNif(n[i], parent, c)

  of nkVarSection:
    c.section = "var"
    for i in 0..<n.len:
      toNif(n[i], parent, c)
  of nkLetSection:
    c.section = "let"
    for i in 0..<n.len:
      toNif(n[i], parent, c)
  of nkConstSection:
    c.section = "const"
    for i in 0..<n.len:
      toNif(n[i], parent, c)

  of nkFormalParams:
    c.section = "param"
    relLineInfo(n, parent, c)
    c.b.addTree(toNifTag(n.kind))
    c.b.writeNodeFlags n.flags
    for i in 0..<n.len:
      toNif(n[i], n, c)
    c.b.endTree
  of nkGenericParams:
    c.section = "typevar"
    relLineInfo(n, parent, c)
    c.b.addTree(toNifTag(n.kind))
    c.b.writeNodeFlags n.flags
    for i in 0..<n.len:
      toNif(n[i], n, c)
    c.b.endTree

  of nkIdentDefs, nkConstDef:
    # multiple ident defs are annoying so we remove them here:
    assert c.section != ""
    let last = n.len-1
    for i in 0..last - 2:
      relLineInfo(n[i], parent, c)
      c.b.addTree(c.section)
      # flatten it further:
      var name: PNode
      var visibility: PNode
      var pragma: PNode
      if n[i].kind == nkPragmaExpr:
        pragma = n[i][1]
        if n[i][0].kind == nkPostfix:
          visibility = n[i][0][0]
          name = n[i][0][1]
        else:
          name = n[i][0]
      elif n[i].kind == nkPostfix:
        visibility = n[i][0]
        name = n[i][1]
      else:
        name = n[i]

      toNifDecl(name, n[i], c) # name

      if visibility != nil:
        c.b.addIdent "x"
      else:
        c.b.addEmpty

      toNifPragmas(pragma, name, n[i], c)

      toNif(n[last-1], n[i], c) # type
      toNif(n[last], n[i], c) # value
      c.b.endTree
  of nkDo:
    relLineInfo(n, parent, c)
    c.b.addTree("do")

    toNif(n[paramsPos], n, c)
    toNif(n[bodyPos], n, c)
    c.b.endTree
  of nkOfInherit:
    if n.len == 1:
      toNif(n[0], parent, c)
    else:
      relLineInfo(n, parent, c)
      c.b.addTree("par")
      for i in 0..<n.len:
        toNif(n[i], n, c)
      c.b.endTree
  of nkOfBranch:
    relLineInfo(n, parent, c)
    c.b.addTree(toNifTag(n.kind))
    c.b.addTree("sconstr")
    for i in 0..<n.len-1:
      toNif(n[i], n, c)
    c.b.endTree

    toNif(n[n.len-1], n, c)
    c.b.endTree

  of nkStmtListType, nkStmtListExpr:
    relLineInfo(n, parent, c)
    c.b.addTree(toNifTag(n.kind))
    c.b.writeNodeFlags n.flags

    c.b.addEmpty # type information of StmtListExpr
    c.b.addTree(toNifTag(n.kind))
    for i in 0..<n.len-1:
      toNif(n[i], n, c)
    c.b.endTree
    if n.len > 0:
      toNif(n[n.len-1], n, c)
    else:
      c.b.addEmpty
    c.b.endTree

  of nkProcTy:
    relLineInfo(n, parent, c)
    c.b.addTree(toNifTag(n.kind))

    c.b.addEmpty 4 # 0: name
    # 1: export marker
    # 2: pattern
    # 3: generics
    if n.len > 0:
      toNif n[0], n, c  # 4: params
    else:
      c.b.addEmpty
    if n.len > 1:
      toNif n[1], n, c  # 5: pragmas
    else:
      c.b.addEmpty

    c.b.addEmpty 2 # 6: exceptions
    # 7: body
    c.b.endTree

  of nkEnumTy:
    # EnumField
    #   SymDef "x"
    #   Empty      # export marker (always empty)
    #   Empty      # pragmas
    #   EnumType
    #   (Integer value, "string value")
    relLineInfo(n, parent, c)
    c.b.addTree(toNifTag(n.kind))
    if n.len > 0:
      assert n[0].kind == nkEmpty
    for i in 1..<n.len:
      let it = n[i]

      var name: PNode
      var val: PNode
      var pragma: PNode

      if it.kind == nkEnumFieldDef:
        let first = it[0]
        if first.kind == nkPragmaExpr:
          name = first[0]
          pragma = first[1]
        else:
          name = it[0]
          pragma = nil
        val = it[1]
      elif it.kind == nkPragmaExpr:
        name = it[0]
        pragma = it[1]
        val = nil
      else:
        name = it
        pragma = nil
        val = nil

      relLineInfo(it, n, c)

      c.b.addTree("efld")
      relLineInfo(it, n, c)
      toNifDecl name, it, c
      c.b.addEmpty # export marker
      toNifPragmas(pragma, name, it, c)
      c.b.addEmpty # type (filled by sema)
      if val == nil:
        c.b.addEmpty
      else:
        toNif(val, it, c)
      c.b.endTree
    c.b.endTree

  of nkProcDef, nkFuncDef, nkConverterDef, nkMacroDef, nkTemplateDef, nkIteratorDef, nkMethodDef:
    relLineInfo(n, parent, c)
    c.b.addTree(toNifTag(n.kind))
    c.b.writeNodeFlags n.flags

    var name: PNode
    var visibility: PNode = nil
    if n[0].kind == nkPostfix:
      visibility = n[0][0]
      name = n[0][1]
    else:
      name = n[0]

    toNifDecl(name, n, c)
    if visibility != nil:
      c.b.addRaw "x"
    else:
      c.b.addEmpty

    for i in 1..<n.len:
      toNif(n[i], n, c)
    c.b.endTree

  of nkVarTuple:
    relLineInfo(n, parent, c)
    assert n[n.len-2].kind == nkEmpty
    c.b.addTree(toNifTag(n.kind))
    c.b.writeNodeFlags n.flags
    toNif(n[n.len-1], n, c)
    c.b.addTree("unpacktuple")
    for i in 0..<n.len-2:
      c.b.addTree(c.section)
      toNifDecl(n[i], n, c) # name
      c.b.addEmpty 4 # 1: export marker
      # 2: pragmas
      # 3: type
      # 4: value
      c.b.endTree
    c.b.endTree
    c.b.endTree

  of nkForStmt:
    relLineInfo(n, parent, c)
    c.b.addTree(toNifTag(n.kind))
    c.b.writeNodeFlags n.flags
    toNif(n[n.len-2], n, c) # iterator
    if n[0].kind == nkVarTuple:
      let v = n[0]
      c.b.addTree("unpacktuple")
      for i in 0..<v.len:
        c.b.addTree("let")
        toNifDecl(v[i], n, c) # name
        c.b.addEmpty 4 # export marker, pragmas, type, value
        c.b.endTree # LetDecl
      c.b.endTree # UnpackIntoTuple
    else:
      c.b.addTree("unpackflat")
      for i in 0..<n.len-2:
        c.b.addTree("let")
        toNifDecl(n[i], n, c) # name
        c.b.addEmpty 4 # export marker, pragmas, type, value
        c.b.endTree # LetDecl
      c.b.endTree # UnpackIntoFlat

    # for-loop-body:
    toNif(n[n.len-1], n, c)
    c.b.endTree

  of nkObjectTy:
    c.section = "fld"
    relLineInfo(n, parent, c)
    c.b.addTree(toNifTag(n.kind))
    c.b.writeNodeFlags n.flags
    for i in 0..<n.len:
      toNif(n[i], n, c)
    c.b.endTree
  else:
    relLineInfo(n, parent, c)
    c.b.addTree(toNifTag(n.kind))
    c.b.writeNodeFlags n.flags
    for i in 0..<n.len:
      toNif(n[i], n, c)
    c.b.endTree

proc initTranslationContext*(conf: ConfigRef): WContext =
  result = WContext(conf: conf, b: nifbuilder.open(500, true))

proc moduleToIr*(n: PNode; c: var WContext) =
  #c.b = nifbuilder.open(100)
  c.b.addHeader "Nifler", "nim-sem"
  toNif(n, nil, c)

proc toNif*(conf: ConfigRef; n: PNode; filename: string) =
  var w = initTranslationContext(conf)
  moduleToIr(n, w)
  writeFile filename, w.b.extract()
  nifindexes.createIndex filename

proc createConf(): ConfigRef =
  result = newConfigRef()
  #result.notes.excl hintLineTooLong
  result.errorMax = 1000

template bench(task, body) =
  when defined(nifBench):
    let t0 = getMonoTime()
    body
    echo task, " TOOK ", getMonoTime() - t0
  else:
    body
