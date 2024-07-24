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

import ".." / lib / [nifbuilder]
import modnames

include tags

type
  Context = object
    conf: ConfigRef
    section: string
    b: Builder

proc absLineInfo(i: TLineInfo; c: var Context) =
  c.b.addLineInfo int32(i.col), int32(i.line), toFullPath(c.conf, i.fileIndex)

proc relLineInfo(n, parent: PNode; c: var Context;
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

proc symToNif(s: PSym; c: var Context; isDef = false) =
  var m = s.name.s & '.' & $s.disamb
  if s.skipGenericOwner().kind == skModule:
    m.add '.'
    m.add moduleSuffix(toFullPath(c.conf, s.info.fileIndex))
  if isDef:
    c.b.addSymbolDef m
  else:
    c.b.addSymbol m

proc toNif*(n, parent: PNode; c: var Context)
proc toNif*(t: PType; parent: PNode; c: var Context)

proc symToNif(n: PNode; parent: PNode; c: var Context; isDef = false) =
  if n.typ != n.sym.typ:
    c.b.withTree "hconv":
      toNif n.typ, parent, c
      symToNif n.sym, c, isDef
  else:
    symToNif n.sym, c, isDef

proc isNominalRef(t: PType): bool {.inline.} =
  let e = t.elementType
  t.sym != nil and e.kind == tyObject and (e.sym == nil or sfAnon in e.sym.flags)

template singleElement(keyw: string) {.dirty.} =
  c.b.withTree keyw:
    if t.hasElementType:
      toNif t.elementType, parent, c
    else:
      c.b.addEmpty

proc toNif*(t: PType; parent: PNode; c: var Context) =
  case t.kind
  of tyNone: c.b.addKeyw typeKindToTag(t.kind)
  of tyBool: c.b.addKeyw typeKindToTag(t.kind)
  of tyChar: c.b.addKeyw "c 8"
  of tyEmpty: c.b.addEmpty
  of tyInt: c.b.addKeyw "i M"
  of tyInt8: c.b.addKeyw "i 8"
  of tyInt16: c.b.addKeyw "i 16"
  of tyInt32: c.b.addKeyw "i 32"
  of tyInt64: c.b.addKeyw "i 64"
  of tyUInt: c.b.addKeyw "u M"
  of tyUInt8: c.b.addKeyw "u 8"
  of tyUInt16: c.b.addKeyw "u 16"
  of tyUInt32: c.b.addKeyw "u 32"
  of tyUInt64: c.b.addKeyw "u 64"
  of tyFloat, tyFloat64: c.b.addKeyw "f 64"
  of tyFloat32: c.b.addKeyw "f 32"
  of tyFloat128: c.b.addKeyw "f 128"
  of tyAlias:
    # XXX Generic aliases are no aliases
    toNif t.skipModifier, parent, c
  of tyNil: c.b.addKeyw typeKindToTag(t.kind)
  of tyUntyped: c.b.addKeyw typeKindToTag(t.kind)
  of tyTyped: c.b.addKeyw typeKindToTag(t.kind)
  of tyTypeDesc:
    c.b.withTree typeKindToTag(t.kind):
      if t.kidsLen == 0 or t.elementType.kind == tyNone:
        c.b.addEmpty
      else:
        toNif t.elementType, parent, c
  of tyGenericParam:
    # See the nim-sem spec:
    c.b.withTree typeKindToTag(t.kind):
      symToNif t.sym, c
      c.b.addIntLit t.sym.position

  of tyGenericInst:
    c.b.withTree typeKindToTag(t.kind):
      toNif t.genericHead, parent, c
      for _, a in t.genericInstParams:
        toNif a, parent, c
  of tyGenericInvocation:
    c.b.withTree typeKindToTag(t.kind):
      toNif t.genericHead, parent, c
      for _, a in t.genericInvocationParams:
        toNif a, parent, c
  of tyGenericBody:
    toNif t.last, parent, c
    # Alternatively something with `genericBodyParams`...
  of tyDistinct, tyEnum:
    symToNif t.sym, c
  of tyPtr:
    if isNominalRef(t):
      symToNif t.sym, c
    else:
      c.b.withTree typeKindToTag(t.kind):
        toNif t.elementType, parent, c
  of tyRef:
    if isNominalRef(t):
      symToNif t.sym, c
    else:
      c.b.withTree typeKindToTag(t.kind):
        toNif t.elementType, parent, c
  of tyVar:
    c.b.withTree(if isOutParam(t): "out" else: "mut"):
      toNif t.elementType, parent, c
  of tyAnd:
    c.b.withTree typeKindToTag(t.kind):
      for _, son in t.ikids: toNif son, parent, c
  of tyOr:
    c.b.withTree typeKindToTag(t.kind):
      for _, son in t.ikids: toNif son, parent, c
  of tyNot:
    c.b.withTree typeKindToTag(t.kind): toNif t.elementType, parent, c

  of tyFromExpr:
    if t.n == nil:
      c.b.addKeyw "err"
    else:
      c.b.withTree typeKindToTag(t.kind):
        toNif t.n, parent, c

  of tyArray:
    c.b.withTree typeKindToTag(t.kind):
      if t.hasElementType:
        toNif t.elementType, parent, c
        toNif t.indexType, parent, c
      else:
        c.b.addEmpty 2
  of tyUncheckedArray:
    c.b.withTree typeKindToTag(t.kind):
      if t.hasElementType:
        toNif t.elementType, parent, c
      else:
        c.b.addEmpty

  of tySequence:
    singleElement typeKindToTag(t.kind)

  of tyOrdinal:
    c.b.withTree typeKindToTag(t.kind):
      if t.hasElementType:
        toNif t.skipModifier, parent, c
      else:
        c.b.addEmpty

  of tySet: singleElement typeKindToTag(t.kind)
  of tyOpenArray: singleElement typeKindToTag(t.kind)
  of tyIterable: singleElement typeKindToTag(t.kind)
  of tyLent: singleElement typeKindToTag(t.kind)

  of tyTuple:
    c.b.withTree typeKindToTag(t.kind):
      if t.n != nil:
        for i in 0..<t.n.len:
          assert(t.n[i].kind == nkSym)
          c.b.withTree "kv":
            c.b.addIdent t.n[i].sym.name.s
            toNif t.n[i].sym.typ, parent, c
      else:
        for _, son in t.ikids: toNif son, parent, c

  of tyRange:
    c.b.withTree typeKindToTag(t.kind):
      toNif t.elementType, parent, c
      if t.n != nil and t.n.kind == nkRange and t.n.len == 2:
        toNif t.n[0], parent, c
        toNif t.n[1], parent, c
      else:
        c.b.addEmpty 2

  of tyProc:
    let kind = if tfIterator in t.flags: "iteratortype"
               else: "proctype"
    c.b.withTree kind:

      c.b.addEmpty # name
      for i, a in t.paramTypes:
        let j = paramTypeToNodeIndex(i)
        if t.n != nil and j < t.n.len and t.n[j].kind == nkSym:
          c.b.addIdent(t.n[j].sym.name.s)
          toNif a, parent, c
      if tfUnresolved in t.flags:
        c.b.addRaw "[*missing parameters*]"
      if t.returnType != nil:
        toNif t.returnType, parent, c
      else:
        c.b.addEmpty

      c.b.withTree "effects":
        # XXX model explicit .raises and .tags annotations
        if tfNoSideEffect in t.flags:
          c.b.addKeyw "noside"
        if tfThread in t.flags:
          c.b.addKeyw "gcsafe"

      c.b.withTree "pragmas":
        if t.callConv == ccNimCall and tfExplicitCallConv notin t.flags:
          discard "no calling convention to generate"
        else:
          c.b.addKeyw ($t.callConv).toLowerAscii.substr(2)

  of tyVarargs:
    c.b.withTree typeKindToTag(t.kind):
      if t.hasElementType:
        toNif t.elementType, parent, c
      else:
        c.b.addEmpty
      if t.n != nil:
        toNif t.n, parent, c
      else:
        c.b.addEmpty

  of tySink: singleElement typeKindToTag(t.kind)
  of tyOwned: singleElement typeKindToTag(t.kind)
  of tyVoid: c.b.addKeyw typeKindToTag(t.kind)
  of tyPointer: c.b.addKeyw typeKindToTag(t.kind)
  of tyString: c.b.addKeyw typeKindToTag(t.kind)
  of tyCstring: c.b.addKeyw typeKindToTag(t.kind)
  of tyObject: symToNif t.sym, c
  of tyForward: c.b.addKeyw typeKindToTag(t.kind)
  of tyProxy: c.b.addKeyw typeKindToTag(t.kind)
  of tyBuiltInTypeClass:
    # XXX See what to do with this.
    c.b.withTree typeKindToTag(t.kind):
      if t.kidsLen == 0 or t.genericHead.kind == tyNone:
        c.b.addEmpty
      else:
        toNif t.genericHead, parent, c

  of tyUserTypeClass, tyConcept:
    # ^ old style concept.  ^ new style concept.
    if t.sym != nil:
      symToNif t.sym, c
    else:
      c.b.addKeyw "err"
  of tyUserTypeClassInst:
    # "instantiated" old style concept. Whatever that even means.
    if t.sym != nil:
      symToNif t.sym, c
    else:
      c.b.addKeyw "err"
  of tyCompositeTypeClass: toNif t.last, parent, c
  of tyInferred: toNif t.skipModifier, parent, c
  of tyAnything: c.b.addKeyw typeKindToTag(t.kind)
  of tyStatic:
    c.b.withTree typeKindToTag(t.kind):
      if t.hasElementType:
        toNif t.skipModifier, parent, c
      else:
        c.b.addEmpty
      if t.n != nil:
        toNif t.n, parent, c
      else:
        c.b.addEmpty

proc toNifDecl(n, parent: PNode; c: var Context) =
  if n.kind == nkSym:
    relLineInfo(n, parent, c)
    symToNif(n, parent, c, true)
  else:
    toNif n, parent, c

proc magicCall(m: TMagic; n: PNode; c: var Context) =
  c.b.addTree(magicToTag(m))
  for i in 1..<n.len:
    toNif(n[i], n, c)
  c.b.endTree

proc toNif*(n, parent: PNode; c: var Context) =
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
      c.b.addTree(nodeKindToTag(n.kind))
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
    c.b.addUIntLit cast[BiggestUInt](n.intVal), "u"
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

    if pragma != nil:
      toNif(pragma, n, c)
    else:
      c.b.addEmpty

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
    c.b.addTree("params")
    for i in 0..<n.len:
      toNif(n[i], n, c)
    c.b.endTree
  of nkGenericParams:
    c.section = "typevar"
    relLineInfo(n, parent, c)
    c.b.addTree("typevars")
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

      if pragma != nil:
        toNif(pragma, n[i], c)
      else:
        c.b.addEmpty

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
    c.b.addTree("of")
    c.b.addTree("sconstr")
    for i in 0..<n.len-1:
      toNif(n[i], n, c)
    c.b.endTree

    toNif(n[n.len-1], n, c)
    c.b.endTree

  of nkStmtListType, nkStmtListExpr:
    relLineInfo(n, parent, c)
    c.b.addTree(nodeKindToTag(n.kind))

    c.b.addEmpty # type information of StmtListExpr
    c.b.addTree("stmts")
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
    c.b.addTree("proctype")

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
    c.b.addTree("enum")
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
      if pragma == nil:
        c.b.addEmpty
      else:
        toNif(pragma, it, c)
      c.b.addEmpty # type (filled by sema)
      if val == nil:
        c.b.addEmpty
      else:
        toNif(val, it, c)
      c.b.endTree
    c.b.endTree

  of nkProcDef, nkFuncDef, nkConverterDef, nkMacroDef, nkTemplateDef, nkIteratorDef, nkMethodDef:
    relLineInfo(n, parent, c)
    c.b.addTree(nodeKindToTag(n.kind))

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
    c.b.addTree(nodeKindToTag(n.kind))
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
    c.b.addTree(nodeKindToTag(n.kind))
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
    c.b.addTree(nodeKindToTag(n.kind))
    for i in 0..<n.len:
      toNif(n[i], n, c)
    c.b.endTree
  else:
    relLineInfo(n, parent, c)
    c.b.addTree(nodeKindToTag(n.kind))
    for i in 0..<n.len:
      toNif(n[i], n, c)
    c.b.endTree

proc initTranslationContext*(conf: ConfigRef): Context =
  result = Context(conf: conf)

proc moduleToIr*(n: PNode; c: var Context) =
  c.b = nifbuilder.open(100)
  c.b.addHeader "Nifler", "nim-sem"
  toNif(n, nil, c)

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
