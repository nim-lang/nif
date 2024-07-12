#       Nifler
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Implements the mapping from Nim AST -> NIF.

when defined(nifBench):
  import std / monotimes

import "$nim" / compiler / [
  ast, options, pathutils, renderer, lineinfos,
  parser, llstream, idents, msgs]

import emitter

proc nodeKindTranslation(k: TNodeKind): string =
  # many of these kinds are never returned by the parser.
  case k
  of nkCommand: "cmd"
  of nkCall: "call"
  of nkCallStrLit: "callstrlit"
  of nkInfix: "infix"
  of nkPrefix: "prefix"
  of nkHiddenCallConv: "<error>"
  of nkExprEqExpr: "vv"
  of nkExprColonExpr: "kv"
  of nkPar: "par"
  of nkObjConstr: "objConstr"
  of nkCurly: "curlyConstr"
  of nkCurlyExpr: "curlyExpr"
  of nkBracket: "bracketConstr"
  of nkBracketExpr: "at"
  of nkPragmaBlock, nkPragmaExpr: "pragmaExpr"
  of nkDotExpr: "dot"
  of nkAsgn, nkFastAsgn: "asgn"
  of nkIfExpr, nkIfStmt: "if"
  of nkWhenStmt, nkRecWhen: "when"
  of nkWhileStmt: "while"
  of nkCaseStmt, nkRecCase: "case"
  of nkForStmt: "for"
  of nkDiscardStmt: "discard"
  of nkBreakStmt: "brk"
  of nkReturnStmt: "ret"
  of nkElifExpr, nkElifBranch: "elif"
  of nkElseExpr, nkElse: "else"
  of nkOfBranch: "of"
  of nkCast: "cast"
  of nkLambda: "proc"
  of nkAccQuoted: "quoted"
  of nkTableConstr: "tableConstr"
  of nkStmtListType, nkStmtListExpr, nkStmtList, nkRecList, nkArgList: "stmts"
  of nkBlockStmt, nkBlockExpr, nkBlockType: "block"
  of nkStaticStmt: "static"
  of nkBind, nkBindStmt: "bind"
  of nkMixinStmt: "mixin"
  of nkAddr: "addr"
  of nkGenericParams: "typevars"
  of nkFormalParams: "params"
  of nkImportAs: "importAs"
  of nkRaiseStmt: "raise"
  of nkContinueStmt: "continue"
  of nkYieldStmt: "yld"
  of nkProcDef: "proc"
  of nkFuncDef: "func"
  of nkMethodDef: "method"
  of nkConverterDef: "converter"
  of nkMacroDef: "macro"
  of nkTemplateDef: "template"
  of nkIteratorDef: "iterator"
  of nkExceptBranch: "except"
  of nkTypeOfExpr: "typeof"
  of nkFinally: "fin"
  of nkTryStmt: "try"
  of nkImportStmt: "import"
  of nkImportExceptStmt: "importExcept"
  of nkIncludeStmt: "include"
  of nkExportStmt: "export"
  of nkExportExceptStmt: "exportExcept"
  of nkFromStmt: "from"
  of nkPragma: "pragmas"
  of nkAsmStmt: "asm"
  of nkDefer: "defer"
  of nkUsingStmt: "using"
  of nkCommentStmt: "comment"
  of nkObjectTy: "object"
  of nkTupleTy, nkTupleClassTy: "tuple"
  of nkTypeClassTy: "concept"
  of nkStaticTy: "staticTy"
  of nkRefTy: "ref"
  of nkPtrTy: "ptr"
  of nkVarTy: "mut"
  of nkDistinctTy: "distinct"
  of nkIteratorTy: "iterTy"
  of nkEnumTy: "enum"
  #of nkEnumFieldDef: EnumFieldDecl
  of nkTupleConstr: "tupleConstr"
  of nkOutTy: "outTy"
  else: "<error>"

type
  TranslationContext = object
    conf: ConfigRef
    section: string

proc absLineInfo(i: TLineInfo; em: var Emitter; c: var TranslationContext) =
  em.addRaw "@"
  em.addLine int32 i.col
  em.addRaw ","
  em.addLine int32 i.line
  em.addRaw ","
  em.addIdent toFullPath(c.conf, i.fileIndex)

proc relLineInfo(n, parent: PNode; em: var Emitter; c: var TranslationContext;
                 emitSpace = false) =
  let i = n.info
  if parent == nil:
    absLineInfo i, em, c
    return
  let p = parent.info
  let colDiff = int32(i.col) - int32(p.col)
  var seps = 0
  if colDiff != 0:
    em.addRaw "@"
    em.addLine colDiff
    seps = 1
  let lineDiff = int32(i.line) - int32(p.line)
  if lineDiff != 0:
    if seps != 1:
      em.addRaw "@"
    seps = 2
    em.addRaw ","
    em.addLine lineDiff
  if i.fileIndex != p.fileIndex:
    case seps
    of 0:
      em.addRaw "@,,"
    of 1:
      em.addRaw ",,"
    of 2:
      em.addRaw ","
    else: discard
    inc seps
    em.addIdent toFullPath(c.conf, i.fileIndex)
  if seps > 0 and emitSpace:
    em.addRaw " "

proc toNif*(n, parent: PNode; em: var Emitter; c: var TranslationContext) =
  case n.kind
  of nkNone, nkEmpty:
    em.addEmpty 1
  of nkNilLit:
    relLineInfo(n, parent, em, c)
    em.addRaw "(nil)"
  of nkStrLit:
    relLineInfo(n, parent, em, c)
    em.addStrLit n.strVal, ""
  of nkRStrLit:
    relLineInfo(n, parent, em, c)
    em.addStrLit n.strVal, "R"
  of nkTripleStrLit:
    relLineInfo(n, parent, em, c)
    em.addStrLit n.strVal, "T"
  of nkCharLit:
    relLineInfo(n, parent, em, c)
    em.addCharLit char(n.intVal)
  of nkIntLit:
    relLineInfo(n, parent, em, c, true)
    em.addIntLit n.intVal
  of nkInt8Lit:
    relLineInfo(n, parent, em, c, true)
    em.addIntLit n.intVal, "i8"
  of nkInt16Lit:
    relLineInfo(n, parent, em, c, true)
    em.addIntLit n.intVal, "i16"
  of nkInt32Lit:
    relLineInfo(n, parent, em, c, true)
    em.addIntLit n.intVal, "i32"
  of nkInt64Lit:
    relLineInfo(n, parent, em, c, true)
    em.addIntLit n.intVal, "i64"
  of nkUIntLit:
    relLineInfo(n, parent, em, c, true)
    em.addUIntLit cast[BiggestUInt](n.intVal), "u"
  of nkUInt8Lit:
    relLineInfo(n, parent, em, c, true)
    em.addUIntLit cast[BiggestUInt](n.intVal), "u8"
  of nkUInt16Lit:
    relLineInfo(n, parent, em, c, true)
    em.addUIntLit cast[BiggestUInt](n.intVal), "u16"
  of nkUInt32Lit:
    relLineInfo(n, parent, em, c, true)
    em.addUIntLit cast[BiggestUInt](n.intVal), "u32"
  of nkUInt64Lit:
    relLineInfo(n, parent, em, c, true)
    em.addUIntLit cast[BiggestUInt](n.intVal), "u64"
  of nkFloatLit:
    relLineInfo(n, parent, em, c, true)
    em.addFloatLit n.floatVal
  of nkFloat32Lit:
    relLineInfo(n, parent, em, c, true)
    em.addFloatLit n.floatVal, "f32"
  of nkFloat64Lit:
    relLineInfo(n, parent, em, c, true)
    em.addFloatLit n.floatVal, "f64"
  of nkFloat128Lit:
    relLineInfo(n, parent, em, c, true)
    em.addFloatLit n.floatVal, "f128"
  of nkIdent:
    relLineInfo(n, parent, em, c, true)
    em.addIdent n.ident.s
  of nkTypeDef:
    relLineInfo(n, parent, em, c)
    var patchPos = em.prepare("type")
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

    addSep em, patchPos
    toNif(name, n, em, c)

    addSep em, patchPos
    if visibility != nil:
      em.addRaw "x"
    else:
      em.addEmpty

    addSep em, patchPos
    if pragma != nil:
      toNif(pragma, n, em, c)
    else:
      em.addEmpty

    for i in 1..<n.len:
      addSep em, patchPos
      toNif(n[i], n, em, c)
    em.patch patchPos

  of nkTypeSection:
    for i in 0..<n.len:
      toNif(n[i], parent, em, c)

  of nkVarSection:
    c.section = "var"
    for i in 0..<n.len:
      toNif(n[i], parent, em, c)
  of nkLetSection:
    c.section = "let"
    for i in 0..<n.len:
      toNif(n[i], parent, em, c)
  of nkConstSection:
    c.section = "const"
    for i in 0..<n.len:
      toNif(n[i], parent, em, c)

  of nkFormalParams:
    c.section = "param"
    relLineInfo(n, parent, em, c)
    var patchPos = em.prepare("params")
    for i in 0..<n.len:
      addSep em, patchPos
      toNif(n[i], n, em, c)
    em.patch patchPos
  of nkGenericParams:
    c.section = "typevar"
    relLineInfo(n, parent, em, c)
    var patchPos = em.prepare("typevars")
    for i in 0..<n.len:
      addSep em, patchPos
      toNif(n[i], n, em, c)
    em.patch patchPos

  of nkIdentDefs, nkConstDef:
    # multiple ident defs are annoying so we remove them here:
    assert c.section != ""
    let last = n.len-1
    for i in 0..last - 2:
      relLineInfo(n[i], parent, em, c)
      var patchPos = em.prepare(c.section)
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

      addSep em, patchPos
      toNif(name, n[i], em, c) # name

      addSep em, patchPos
      if visibility != nil:
        em.addRaw "x"
      else:
        em.addEmpty

      addSep em, patchPos
      if pragma != nil:
        toNif(pragma, n[i], em, c)
      else:
        em.addEmpty

      addSep em, patchPos
      toNif(n[last-1], n[i], em, c) # type

      addSep em, patchPos
      toNif(n[last], n[i], em, c) # value
      em.patch patchPos
  of nkDo:
    relLineInfo(n, parent, em, c)
    var patchPos = em.prepare("paramsAndBody")
    addSep em, patchPos
    toNif(n[paramsPos], n, em, c)
    addSep em, patchPos
    toNif(n[bodyPos], n, em, c)
    em.patch patchPos
  of nkOfInherit:
    if n.len == 1:
      toNif(n[0], parent, em, c)
    else:
      relLineInfo(n, parent, em, c)
      var patchPos = em.prepare("par")
      for i in 0..<n.len:
        addSep em, patchPos
        toNif(n[i], n, em, c)
      em.patch patchPos
  of nkOfBranch:
    relLineInfo(n, parent, em, c)
    var patchPos = em.prepare("of")
    var patchPosB = em.prepare("curlyConstr")
    for i in 0..<n.len-1:
      addSep em, patchPosB
      toNif(n[i], n, em, c)
    em.patch patchPosB
    addSep em, patchPos
    toNif(n[n.len-1], n, em, c)
    em.patch patchPos

  of nkStmtListType, nkStmtListExpr:
    relLineInfo(n, parent, em, c)
    var patchPos = em.prepare("expr")
    em.addSep patchPos
    em.addEmpty # type information of StmtListExpr
    var patchPosB = em.prepare("stmts")
    for i in 0..<n.len-1:
      em.addSep patchPosB
      toNif(n[i], n, em, c)
    em.patch patchPosB
    if n.len > 0:
      em.addSep patchPos
      toNif(n[n.len-1], n, em, c)
    else:
      em.addEmpty
    em.patch patchPos

  of nkProcTy:
    relLineInfo(n, parent, em, c)
    var patchPos = em.prepare("procTy")

    em.addSep patchPos
    em.addEmpty 4 # 0: name
    # 1: export marker
    # 2: pattern
    # 3: generics

    em.addSep patchPos
    if n.len > 0:
      toNif n[0], n, em, c  # 4: params
    else:
      em.addEmpty

    em.addSep patchPos
    if n.len > 1:
      toNif n[1], n, em, c  # 5: pragmas
    else:
      em.addEmpty

    em.addSep patchPos
    em.addEmpty 2 # 6: exceptions
    # 7: body
    em.patch patchPos

  of nkEnumTy:
    # EnumField
    #   SymDef "x"
    #   Empty      # export marker (always empty)
    #   Empty      # pragmas
    #   EnumType
    #   (Integer value, "string value")
    relLineInfo(n, parent, em, c)
    var patchPos = em.prepare("enum")
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

      relLineInfo(it, n, em, c)

      var patchPosB = em.prepare("enumFieldDecl")
      relLineInfo(it, n, em, c)

      em.addSep patchPosB
      toNif name, it, em, c

      em.addSep patchPosB
      em.addEmpty # export marker

      em.addSep patchPosB
      if pragma == nil:
        em.addEmpty
      else:
        toNif(pragma, it, em, c)

      em.addSep patchPosB
      em.addEmpty # type (filled by sema)

      em.addSep patchPosB
      if val == nil:
        em.addEmpty
      else:
        toNif(val, it, em, c)
      em.patch patchPosB

    em.patch patchPos

  of nkProcDef, nkFuncDef, nkConverterDef, nkMacroDef, nkTemplateDef, nkIteratorDef, nkMethodDef:
    relLineInfo(n, parent, em, c)
    var patchPos = em.prepare(nodeKindTranslation(n.kind))

    var name: PNode
    var visibility: PNode = nil
    if n[0].kind == nkPostfix:
      visibility = n[0][0]
      name = n[0][1]
    else:
      name = n[0]

    addSep em, patchPos
    toNif(name, n, em, c)

    addSep em, patchPos
    if visibility != nil:
      em.addRaw "x"
    else:
      em.addEmpty

    for i in 1..<n.len:
      addSep em, patchPos
      toNif(n[i], n, em, c)
    em.patch patchPos

  of nkVarTuple:
    relLineInfo(n, parent, em, c)
    assert n[n.len-2].kind == nkEmpty
    var patchPos = em.prepare("unpackDecl")
    toNif(n[n.len-1], n, em, c)

    em.addSep patchPos
    var patchPosU = em.prepare("unpackIntoTuple")
    for i in 0..<n.len-2:
      var patchPosB = em.prepare(c.section)
      toNif(n[i], n, em, c) # name

      em.addSep patchPosB
      em.addEmpty 4 # 1: export marker
      # 2: pragmas
      # 3: type
      # 4: value
      em.patch patchPosB
    em.patch patchPosU
    em.patch patchPos

  of nkForStmt:
    relLineInfo(n, parent, em, c)
    var patchPos = em.prepare("for")

    em.addSep patchPos
    toNif(n[n.len-2], n, em, c) # iterator

    if n[0].kind == nkVarTuple:
      let v = n[0]
      var patchPosB = em.prepare("unpackIntoTuple")
      for i in 0..<v.len:
        var patchPosD = em.prepare("let")

        em.addSep patchPosD
        toNif(v[i], n, em, c) # name

        em.addSep patchPosD
        em.addEmpty 4 # export marker, pragmas, type, value
        em.patch patchPosD # LetDecl
      em.patch patchPosB # UnpackIntoTuple
    else:
      var patchPosC = em.prepare("unpackIntoFlat")
      for i in 0..<n.len-2:
        var patchPosD = em.prepare("let")

        em.addSep patchPosD
        toNif(n[i], n, em, c) # name

        em.addSep patchPosD
        em.addEmpty 4 # export marker, pragmas, type, value
        em.patch patchPosD # LetDecl
      em.patch patchPosC # UnpackIntoFlat

    # for-loop-body:
    em.addSep patchPos
    toNif(n[n.len-1], n, em, c)
    em.patch patchPos

  of nkObjectTy:
    c.section = "fld"
    relLineInfo(n, parent, em, c)
    var patchPos = em.prepare(nodeKindTranslation(n.kind))

    em.addSep patchPos
    em.addEmpty # objectTagPos

    for i in 0..<n.len:
      em.addSep patchPos
      toNif(n[i], n, em, c)
    em.patch patchPos
  else:
    relLineInfo(n, parent, em, c)
    var patchPos = em.prepare(nodeKindTranslation(n.kind))
    for i in 0..<n.len:
      em.addSep patchPos
      toNif(n[i], n, em, c)
    em.patch patchPos

proc initTranslationContext*(conf: ConfigRef): TranslationContext =
  result = TranslationContext(conf: conf)

proc moduleToIr*(n: PNode; em: var Emitter; c: var TranslationContext) =
  var ver = em.prepare ".nif24"
  em.patchDir ver
  var vendor = em.prepare ".vendor"
  em.addSep vendor
  em.addStrLit "Nifler", ""
  em.patchDir vendor
  var dialect = em.prepare ".dialect"
  em.addSep dialect
  em.addStrLit "nim-parsed", ""
  em.patchDir dialect
  toNif(n, nil, em, c)

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

proc parseFile*(em: var Emitter; thisfile: string) =
  let stream = llStreamOpen(AbsoluteFile thisfile, fmRead)
  if stream == nil:
    quit "cannot open file: " & thisfile
  else:
    var conf = createConf()
    var parser: Parser
    openParser(parser, AbsoluteFile(thisfile), stream, newIdentCache(), conf)
    var tc = initTranslationContext(conf)

    bench "parseAll":
      let fullTree = parseAll(parser)

    bench "moduleToIr":
      moduleToIr(fullTree, em, tc)
    closeParser(parser)
