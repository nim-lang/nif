#       Nifler
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Implements the mapping from Nim sem's AST to NIF ("nim-sem").

when defined(nifBench):
  import std / monotimes

import std / [strutils]

import "$nim" / compiler / [
  ast, options, pathutils, renderer, lineinfos,
  parser, llstream, idents, msgs]

import ".." / lib / [nifbuilder]
import modnames

proc nodeKindTranslation(k: TNodeKind): string =
  # many of these kinds are never returned by the parser.
  case k
  of nkCommand: "cmd"
  of nkCall: "call"
  of nkCallStrLit: "callstrlit"
  of nkInfix: "infix"
  of nkPrefix: "prefix"
  of nkHiddenCallConv: "hcall"
  of nkExprEqExpr: "vv"
  of nkExprColonExpr: "kv"
  of nkPar: "par"
  of nkObjConstr: "oconstr"
  of nkCurly: "sconstr"
  of nkCurlyExpr: "curlyexpr"
  of nkBracket: "aconstr"
  of nkBracketExpr: "at"
  of nkPragmaBlock, nkPragmaExpr: "pragmaexpr"
  of nkDotExpr: "dot"
  of nkAsgn: "asgn"
  of nkFastAsgn: "fasgn"
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
  of nkTableConstr: "tableconstr"
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
  of nkYieldStmt: "yield"
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
  of nkImportExceptStmt: "importexcept"
  of nkIncludeStmt: "include"
  of nkExportStmt: "export"
  of nkExportExceptStmt: "exportexcept"
  of nkFromStmt: "from"
  of nkPragma: "pragmas"
  of nkAsmStmt: "asm"
  of nkDefer: "defer"
  of nkUsingStmt: "using"
  of nkCommentStmt: "comment"
  of nkObjectTy: "object"
  of nkTupleTy, nkTupleClassTy: "tuple"
  of nkTypeClassTy: "concept"
  of nkStaticTy: "stat"
  of nkRefTy: "ref"
  of nkPtrTy: "ptr"
  of nkVarTy: "mut"
  of nkDistinctTy: "distinct"
  of nkIteratorTy: "itert"
  of nkEnumTy: "enum"
  #of nkEnumFieldDef: EnumFieldDecl
  of nkTupleConstr: "tupleconstr"
  of nkOutTy: "outTy"
  of nkType: "<error>" # should follow n.typ instead

  of nkNone, nkEmpty, nkIdent, nkCharLit, nkIntLit, nkInt8Lit, nkInt16Lit,
     nkInt32Lit, nkInt64Lit, nkUIntLit, nkUInt8Lit, nkUInt16Lit, nkUInt32Lit,
     nkUInt64Lit, nkFloatLit, nkFloat32Lit, nkFloat64Lit, nkFloat128Lit,
     nkStrLit, nkRStrLit, nkTripleStrLit, nkNilLit, nkSym:
    "<error>" # Atom: handled as a special case
  of nkComesFrom: "comesfrom"
  of nkDotCall: "dotcall"
  of nkPostfix: "postfix"
  of nkIdentDefs: "<error>" # eliminated in nim-sem
  of nkVarTuple: "vartuple"
  of nkRange: "range"
  of nkCheckedFieldExpr: "xdot"
  of nkDerefExpr: "deref"
  of nkDo: "do"
  of nkClosedSymChoice: "cchoice"
  of nkOpenSymChoice: "ochoice"
  of nkHiddenStdConv: "hstdconv"
  of nkHiddenSubConv: "hsubconv"
  of nkConv: "conv"
  of nkStaticExpr: "static"
  of nkHiddenAddr: "haddr"
  of nkHiddenDeref: "hderef"
  of nkObjDownConv: "downconv"
  of nkObjUpConv: "upconv"
  of nkChckRangeF: "xrangef"
  of nkChckRange64: "xrange64"
  of nkChckRange: "xrange"
  of nkStringToCString: "tocstr"
  of nkCStringToString: "tostr"
  of nkOfInherit: "ofh"
  of nkParForStmt: "parfor"
  of nkTypeSection, nkVarSection, nkLetSection, nkConstSection:
    "<error>" # not a thing in nim-sem
  of nkConstDef: "const"
  of nkTypeDef: "type"
  of nkWith: "with"
  of nkWithout: "without"
  of nkConstTy: "ro"
  of nkProcTy: "proctype"
  of nkSinkAsgn: "snk"
  of nkEnumFieldDef: "efld"
  of nkPattern: "trpattern"
  of nkHiddenTryStmt: "htry"
  of nkClosure: "closure"
  of nkGotoState: "gotostate"
  of nkState: "state"
  of nkBreakState: "brstate"
  of nkError: "err"
  of nkModuleRef: "modref"
  of nkReplayAction: "replay"
  of nkNilRodNode: "nilrod"


type
  TranslationContext = object
    conf: ConfigRef
    section: string
    b: Builder

proc absLineInfo(i: TLineInfo; c: var TranslationContext) =
  c.b.addLineInfo int32(i.col), int32(i.line), toFullPath(c.conf, i.fileIndex)

proc relLineInfo(n, parent: PNode; c: var TranslationContext;
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

proc symToNif(s: PSym; c: var TranslationContext; isDef = false) =
  var m = s.name.s & '.' & $s.disamb
  if s.skipGenericOwner().kind == skModule:
    m.add '.'
    m.add moduleSuffix(toFullPath(c.conf, s.info.fileIndex))
  if isDef:
    c.b.addSymbolDef m
  else:
    c.b.addSymbol m

proc toNif*(n, parent: PNode; c: var TranslationContext)
proc toNif*(t: PType; parent: PNode; c: var TranslationContext)

proc symToNif(n: PNode; parent: PNode; c: var TranslationContext; isDef = false) =
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

proc toNif*(t: PType; parent: PNode; c: var TranslationContext) =
  case t.kind
  of tyNone: c.b.addKeyw "err"
  of tyBool: c.b.addKeyw "bool"
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
  of tyNil: c.b.addKeyw "nilt"
  of tyUntyped: c.b.addKeyw "untyped"
  of tyTyped: c.b.addKeyw "typed"
  of tyTypeDesc:
    c.b.withTree "typedesc":
      if t.kidsLen == 0 or t.elementType.kind == tyNone:
        c.b.addEmpty
      else:
        toNif t.elementType, parent, c
  of tyGenericParam:
    # See the nim-sem spec:
    c.b.withTree "p":
      symToNif t.sym, c
      c.b.addIntLit t.sym.position

  of tyGenericInst:
    c.b.withTree "inst":
      toNif t.genericHead, parent, c
      for _, a in t.genericInstParams:
        toNif a, parent, c
  of tyGenericInvocation:
    c.b.withTree "invok":
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
      c.b.withTree "ptr":
        toNif t.elementType, parent, c
  of tyRef:
    if isNominalRef(t):
      symToNif t.sym, c
    else:
      c.b.withTree "ref":
        toNif t.elementType, parent, c
  of tyVar:
    c.b.withTree(if isOutParam(t): "out" else: "mut"):
      toNif t.elementType, parent, c
  of tyAnd:
    c.b.withTree "and":
      for _, son in t.ikids: toNif son, parent, c
  of tyOr:
    c.b.withTree "or":
      for _, son in t.ikids: toNif son, parent, c
  of tyNot:
    c.b.withTree "not": toNif t.elementType, parent, c

  of tyFromExpr:
    if t.n == nil:
      c.b.addKeyw "err"
    else:
      c.b.withTree "typeof":
        toNif t.n, parent, c

  of tyArray:
    c.b.withTree "array":
      if t.hasElementType:
        toNif t.elementType, parent, c
        toNif t.indexType, parent, c
      else:
        c.b.addEmpty 2
  of tyUncheckedArray:
    c.b.withTree "uarray":
      if t.hasElementType:
        toNif t.elementType, parent, c
      else:
        c.b.addEmpty

  of tySequence:
    singleElement "seq"

  of tyOrdinal:
    c.b.withTree "ordinal":
      if t.hasElementType:
        toNif t.skipModifier, parent, c
      else:
        c.b.addEmpty

  of tySet: singleElement "set"
  of tyOpenArray: singleElement "oarray"
  of tyIterable: singleElement "iterable"
  of tyLent: singleElement "lent"

  of tyTuple:
    c.b.withTree "tuple":
      if t.n != nil:
        for i in 0..<t.n.len:
          assert(t.n[i].kind == nkSym)
          c.b.withTree "kv":
            c.b.addIdent t.n[i].sym.name.s
            toNif t.n[i].sym.typ, parent, c
      else:
        for _, son in t.ikids: toNif son, parent, c

  of tyRange:
    c.b.withTree "range":
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
    c.b.withTree "varargs":
      if t.hasElementType:
        toNif t.elementType, parent, c
      else:
        c.b.addEmpty
      if t.n != nil:
        toNif t.n, parent, c
      else:
        c.b.addEmpty

  of tySink: singleElement "sink"
  of tyOwned: singleElement "owned"
  of tyVoid: c.b.addKeyw "void"
  of tyPointer: c.b.addKeyw "pointer"
  of tyString: c.b.addKeyw "str"
  of tyCstring: c.b.addKeyw "cstr"
  of tyObject: symToNif t.sym, c
  of tyForward: c.b.addKeyw "forward"
  of tyProxy: c.b.addKeyw "err"
  of tyBuiltInTypeClass:
    # XXX See what to do with this.
    c.b.withTree "typeclass":
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
  of tyAnything: c.b.addKeyw "any"
  of tyStatic:
    c.b.withTree "stat":
      if t.hasElementType:
        toNif t.skipModifier, parent, c
      else:
        c.b.addEmpty
      if t.n != nil:
        toNif t.n, parent, c
      else:
        c.b.addEmpty

proc toNifDecl(n, parent: PNode; c: var TranslationContext) =
  if n.kind == nkSym:
    relLineInfo(n, parent, c)
    symToNif(n, parent, c, true)
  else:
    toNif n, parent, c

proc magicToKind(m: TMagic): string =
  case m
  of mNone: "<cannot happen>"
  of mArray: "array"
  of mOpenArray: "oarray"
  of mRange: "range"
  of mSet: "set"
  of mSeq: "seq"
  of mVarargs: "varargs"
  of mRef: "ref"
  of mPtr: "ptr"
  of mVar: "mut"
  of mVoid, mVoidType: "void"
  of mIterableType: "iterable"
  of mType: "typeof"
  of mUncheckedArray: "uarray"
  of mAppendStrCh: "addc"
  of mAppendStrStr: "adds"
  of mAppendSeqElem: "adde"
  of mInSet: "contains"
  of mSetLengthStr: "ssetlen"
  of mSetLengthSeq: "qsetlen"
  of mLengthOpenArray: "olen"
  of mLengthStr: "slen"
  of mLengthArray: "alen"
  of mLengthSeq: "qlen"
  else:
    let s = $m
    if s.endsWith"F64":
      s.substr(1, s.len-4).toLowerAscii
    else:
      s.substr(1, s.len-1).toLowerAscii

proc magicCall(m: TMagic; n: PNode; c: var TranslationContext) =
  c.b.addTree(magicToKind(m))
  for i in 1..<n.len:
    toNif(n[i], n, c)
  c.b.endTree

proc toNif*(n, parent: PNode; c: var TranslationContext) =
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
      c.b.addTree(nodeKindTranslation(n.kind))
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
    c.b.addTree("expr")

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
    c.b.addTree(nodeKindTranslation(n.kind))

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
    c.b.addTree("unpackdecl")
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
    c.b.addTree("for")
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
    c.b.addTree(nodeKindTranslation(n.kind))
    for i in 0..<n.len:
      toNif(n[i], n, c)
    c.b.endTree
  else:
    relLineInfo(n, parent, c)
    c.b.addTree(nodeKindTranslation(n.kind))
    for i in 0..<n.len:
      toNif(n[i], n, c)
    c.b.endTree

proc initTranslationContext*(conf: ConfigRef): TranslationContext =
  result = TranslationContext(conf: conf)

proc moduleToIr*(n: PNode; c: var TranslationContext) =
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
