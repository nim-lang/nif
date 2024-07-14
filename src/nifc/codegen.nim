#
#
#           NIFC Compiler
#        (c) Copyright 2024 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# We produce C code as a list of tokens.

import std / [assertions, syncio, tables, intsets, formatfloat]
import .. / lib / [bitabs, packedtrees]
import mangler, nifc_model

type
  Token = distinct uint32

proc `==`(a, b: Token): bool {.borrow.}

type
  PredefinedToken = enum
    IgnoreMe = "<unused>"
    EmptyToken = ""
    CurlyLe = "{"
    CurlyRi = "}"
    ParLe = "("
    ParRi = ")"
    BracketLe = "["
    BracketRi = "]"
    NewLine = "\n"
    Semicolon = ";"
    Comma = ", "
    Space = " "
    Colon = ": "
    Dot = "."
    Arrow = "->"
    Star = "*"
    Amp = "&"
    AsgnOpr = " = "
    ScopeOpr = "::"
    ConstKeyword = "const "
    StaticKeyword = "static "
    ExternKeyword = "extern "
    WhileKeyword = "while "
    IfKeyword = "if ("
    ElseKeyword = "else "
    SwitchKeyword = "switch "
    CaseKeyword = "case "
    DefaultKeyword = "default:"
    BreakKeyword = "break"
    NullPtr = "nullptr"
    IfNot = "if (!("
    ReturnKeyword = "return "
    TypedefStruct = "typedef struct "
    TypedefUnion = "typedef union "
    IncludeKeyword = "#include "

proc fillTokenTable(tab: var BiTable[Token, string]) =
  for e in EmptyToken..high(PredefinedToken):
    let id = tab.getOrIncl $e
    assert id == Token(e), $(id, " ", ord(e))

type
  GeneratedCode* = object
    m: Module
    includes: seq[Token]
    includedHeaders: IntSet
    data: seq[Token]
    protos: seq[Token]
    code: seq[Token]
    init: seq[Token]
    tokens: BiTable[Token, string]
    emittedStrings: IntSet
    needsPrefix: IntSet
    generatedTypes: IntSet

proc initGeneratedCode*(m: sink Module): GeneratedCode =
  result = GeneratedCode(m: m, code: @[], tokens: initBiTable[Token, string]())
  fillTokenTable(result.tokens)

proc add*(g: var GeneratedCode; t: PredefinedToken) {.inline.} =
  g.code.add Token(t)

proc add*(g: var GeneratedCode; s: string) {.inline.} =
  g.code.add g.tokens.getOrIncl(s)

type
  CppFile = object
    f: File

proc write(f: var CppFile; s: string) = write(f.f, s)
proc write(f: var CppFile; c: char) = write(f.f, c)

proc writeTokenSeq(f: var CppFile; s: seq[Token]; c: GeneratedCode) =
  var indent = 0
  for i in 0..<s.len:
    let x = s[i]
    case x
    of Token(CurlyLe):
      inc indent
      write f, c.tokens[x]
      write f, "\n"
      for i in 1..indent*2: write f, ' '
    of Token(CurlyRi):
      dec indent
      write f, c.tokens[x]
      if i+1 < s.len and s[i+1] == Token(CurlyRi):
        discard
      else:
        write f, "\n"
        for i in 1..indent*2: write f, ' '
    of Token(Semicolon):
      write f, c.tokens[x]
      if i+1 < s.len and s[i+1] == Token(CurlyRi):
        discard "no newline before }"
      else:
        write f, "\n"
        for i in 1..indent*2: write f, ' '
    of Token(NewLine):
      write f, c.tokens[x]
      for i in 1..indent*2: write f, ' '
    else:
      write f, c.tokens[x]

proc error(m: Module; msg: string; id: StrId) =
  write stdout, msg
  writeLine stdout, m.lits.strings[id]
  quit 1

# Type graph

type
  TypeList = object
    processed: IntSet
    s: seq[(TypeId, PredefinedToken)]

proc add(dest: var TypeList; elem: TypeId; decl: PredefinedToken) =
  if not containsOrIncl(dest.processed, int(elem)):
    dest.s.add (elem, decl)

type
  TypeOrder = object
    forwardedDecls, ordered: TypeList
    lookedAt, lookedAtBodies: IntSet

proc traverseObjectBody(m: Module; c: var TypeOrder; t: TypeId)

proc recordDependency(m: Module; c: var TypeOrder; parent, child: TypeId) =
  var ch = child
  var viaPointer = false
  while true:
    case m.types[ch].kind
    of APtrC, PtrC:
      viaPointer = true
      ch = elementType(m.types, ch)
    of FlexarrayC:
      ch = elementType(m.types, ch)
    else:
      break

  case m.types[ch].kind
  of ObjectC, UnionC:
    let decl = if m.types[ch].kind == ObjectC: TypedefStruct else: TypedefUnion
    let obj = ch
    if viaPointer:
      c.forwardedDecls.add parent, decl
    else:
      if not containsOrIncl(c.lookedAt, obj.int):
        traverseObjectBody(m, c, obj)
      c.ordered.add obj, decl
  of ArrayC:
    if viaPointer:
      c.forwardedDecls.add parent, TypedefStruct
    else:
      if not containsOrIncl(c.lookedAt, ch.int):
        traverseObjectBody(m, c, ch)
      c.ordered.add ch, TypedefStruct
  of Sym:
    # follow the symbol to its definition:
    let id = m.types[ch].litId
    let def = m.defs.getOrDefault(id)
    if def == NodePos(0):
      error m, "undeclared symbol: ", id
    else:
      let decl = asTypeDecl(m.types, def)
      if not containsOrIncl(c.lookedAtBodies, decl.body.int):
        recordDependency m, c, parent, decl.body
  else:
    discard "uninteresting type as we only focus on the required struct declarations"

proc traverseObjectBody(m: Module; c: var TypeOrder; t: TypeId) =
  for x in sons(m.types, t):
    case m.types[x].kind
    of FldC:
      let decl = asFieldDecl(m.types, x)
      recordDependency m, c, t, decl.typ
    of Sym:
      # inheritance
      recordDependency m, c, t, x
    else: discard

proc traverseTypes(m: Module; c: var TypeOrder) =
  for ch in sons(m.types, StartPos):
    let decl = asTypeDecl(m.types, ch)
    let t = decl.body
    case m.types[t].kind
    of ObjectC:
      traverseObjectBody m, c, t
      c.ordered.add ch, TypedefStruct
    of UnionC:
      traverseObjectBody m, c, t
      c.ordered.add ch, TypedefUnion
    of ArrayC:
      traverseObjectBody m, c, t
      c.ordered.add ch, TypedefStruct
    else: discard

proc genType(g: var GeneratedCode; types: TypeGraph; lit: Literals; t: TypeId; name = "") =
  template maybeAddName =
    if name != "":
      g.add Space
      g.add name

  template atom(s: string) =
    g.add s
    maybeAddName()
  case types[t].kind
  of VoidC: atom "void"
  of IntC: atom "NI" & $types[t].integralBits
  of UIntTy: atom "NU" & $types[t].integralBits
  of FloatTy: atom "NF" & $types[t].integralBits
  of BoolTy: atom "NB" & $types[t].integralBits
  of CharTy: atom "NC" & $types[t].integralBits
  of ObjectTy, UnionTy, NameVal, AnnotationVal:
    atom lit.strings[types[t].litId]
  of VarargsTy:
    g.add "..."
  of APtrTy, UPtrTy, AArrayPtrTy, UArrayPtrTy:
    genType g, types, lit, elementType(types, t)
    g.add Star
    maybeAddName()
  of ArrayTy:
    genType g, types, lit, arrayName(types, t)
    maybeAddName()
  of LastArrayTy:
    genType g, types, lit, elementType(types, t)
    maybeAddName()
    g.add BracketLe
    g.add BracketRi
  of ProcTy:
    let (retType, callConv) = returnType(types, t)
    genType g, types, lit, retType
    g.add Space
    g.add ParLe
    genType g, types, lit, callConv
    g.add Star # "(*fn)"
    maybeAddName()
    g.add ParRi
    g.add ParLe
    var i = 0
    for ch in params(types, t):
      if i > 0: g.add Comma
      genType g, types, lit, ch
      inc i
    g.add ParRi
  of ObjectDecl, UnionDecl:
    atom lit.strings[types[t.firstSon].litId]
  of IntVal, SizeVal, AlignVal, OffsetVal, FieldDecl:
    #raiseAssert "did not expect: " & $types[t].kind
    g.add "BUG "
    atom $types[t].kind

proc generateTypes(g: var GeneratedCode; types: TypeGraph; lit: Literals; c: TypeOrder) =
  for (t, declKeyword) in c.forwardedDecls.s:
    let name = if types[t].kind == ArrayTy: arrayName(types, t) else: t.firstSon
    let s {.cursor.} = lit.strings[types[name].litId]
    g.add declKeyword
    g.add s
    g.add Space
    g.add s
    g.add Semicolon

  for (t, declKeyword) in c.ordered.s:
    let name = if types[t].kind == ArrayTy: arrayName(types, t) else: t.firstSon
    let litId = types[name].litId
    if not g.generatedTypes.containsOrIncl(litId.int):
      let s {.cursor.} = lit.strings[litId]
      g.add declKeyword
      g.add CurlyLe
      if types[t].kind == ArrayTy:
        genType g, types, lit, elementType(types, t), "a"
        g.add BracketLe
        g.add $arrayLen(types, t)
        g.add BracketRi
        g.add Semicolon
      else:
        var i = 0
        for x in sons(types, t):
          case types[x].kind
          of FieldDecl:
            genType g, types, lit, x.firstSon, "F" & $i
            g.add Semicolon
            inc i
          of ObjectTy:
            genType g, types, lit, x, "P"
            g.add Semicolon
          else: discard
      g.add CurlyRi
      g.add s
      g.add Semicolon

# Procs

template emitData(s: string) = c.data.add c.tokens.getOrIncl(s)
template emitData(t: Token) = c.data.add t
template emitData(t: PredefinedToken) = c.data.add Token(t)

proc genStrLit(c: var GeneratedCode; lit: Literals; litId: Token): Token =
  result = Token(c.tokens.getOrIncl "QStr" & $litId)
  if not containsOrIncl(c.emittedStrings, int(litId)):
    let s {.cursor.} = lit.strings[litId]
    emitData "static const struct "
    emitData CurlyLe
    emitData "NI cap"
    emitData Semicolon
    emitData "NC8 data"
    emitData BracketLe
    emitData $s.len
    emitData "+1"
    emitData BracketRi
    emitData Semicolon
    emitData CurlyRi
    emitData result
    emitData AsgnOpr
    emitData CurlyLe
    emitData $s.len
    emitData " | NIM_STRLIT_FLAG"
    emitData Comma
    emitData makeCString(s)
    emitData CurlyRi
    emitData Semicolon

proc genIntLit(c: var GeneratedCode; lit: Literals; litId: Token) =
  let i = lit.numbers[litId]
  if i > low(int32) and i <= high(int32):
    c.add $i
  elif i == low(int32):
    # Nim has the same bug for the same reasons :-)
    c.add "(-2147483647 -1)"
  elif i > low(int64):
    c.add "IL64("
    c.add $i
    c.add ")"
  else:
    c.add "(IL64(-9223372036854775807) - IL64(1))"

proc gen(c: var GeneratedCode; t: Tree; n: NodePos)

proc genDisplayName(c: var GeneratedCode; symId: SymId) =
  let displayName = c.m.symnames[symId]
  if displayName != Token(0):
    c.add "/*"
    c.add c.m.lit.strings[displayName]
    c.add "*/"

proc genSymDef(c: var GeneratedCode; t: Tree; n: NodePos) =
  if t[n].kind == SymDef:
    let symId = t[n].symId
    c.needsPrefix.incl symId.int
    genDisplayName c, symId
  gen c, t, n

proc genGlobal(c: var GeneratedCode; t: Tree; name, typ: NodePos; annotation: string) =
  c.add annotation
  let m: string
  if t[name].kind == SymDef:
    let symId = t[name].symId
    m = c.tokens[mangleModuleName(c, c.m.namespace)] & "__" & $symId
    genDisplayName c, symId
  else:
    assert t[name].kind == ModuleSymUse
    let (x, y) = sons2(t, name)
    m = c.tokens[mangleModuleName(c, t[x].litId)] & "__" & $t[y].immediateVal
  genType c, c.m.types, c.m.lit, t[typ].typeId, m

proc genLocal(c: var GeneratedCode; t: Tree; name, typ: NodePos; annotation: string) =
  assert t[name].kind == SymDef
  c.add annotation
  let symId = t[name].symId
  genType c, c.m.types, c.m.lit, t[typ].typeId, "q" & $symId
  genDisplayName c, symId

proc genProcDecl(c: var GeneratedCode; t: Tree; n: NodePos; isExtern: bool) =
  let signatureBegin = c.code.len
  let name = n.firstSon

  var prc = n.firstSon
  next t, prc

  while true:
    case t[prc].kind
    of PragmaPair:
      let (x, y) = sons2(t, prc)
      let key = cast[PragmaKey](t[x].rawOperand)
      case key
      of HeaderImport:
        let lit = t[y].litId
        let headerAsStr {.cursor.} = c.m.lit.strings[lit]
        let header = c.tokens.getOrIncl(headerAsStr)
        # headerAsStr can be empty, this has the semantics of the `nodecl` pragma:
        if headerAsStr.len > 0 and not c.includedHeaders.containsOrIncl(int header):
          if headerAsStr[0] == '#':
            discard "skip the #include"
          else:
            c.includes.add Token(IncludeKeyword)
          c.includes.add header
          c.includes.add Token NewLine
        # do not generate code for importc'ed procs:
        return
      of DllImport:
        let lit = t[y].litId
        raiseAssert "cannot eval: " & c.m.lit.strings[lit]
      else: discard
    of PragmaId: discard
    else: break
    next t, prc

  var resultDeclPos = NodePos(-1)
  if t[prc].kind == SummonResult:
    resultDeclPos = prc
    gen c, t, prc.firstSon
    next t, prc
  else:
    c.add "void"
  c.add Space
  genSymDef c, t, name
  c.add ParLe
  var params = 0
  while t[prc].kind == SummonParam:
    if params > 0: c.add Comma
    let (typ, sym) = sons2(t, prc)
    genLocal c, t, sym, typ, ""
    next t, prc
    inc params
  if params == 0:
    c.add "void"
  c.add ParRi

  for i in signatureBegin ..< c.code.len:
    c.protos.add c.code[i]
  c.protos.add Token Semicolon

  if isExtern:
    c.code.setLen signatureBegin
  else:
    c.add CurlyLe
    if resultDeclPos.int >= 0:
      gen c, t, resultDeclPos
    for ch in sonsRest(t, n, prc):
      gen c, t, ch
    c.add CurlyRi

template triop(opr) =
  let (typ, a, b) = sons3(t, n)
  c.add ParLe
  c.add ParLe
  gen c, t, typ
  c.add ParRi
  gen c, t, a
  c.add opr
  gen c, t, b
  c.add ParRi

template cmpop(opr) =
  let (_, a, b) = sons3(t, n)
  c.add ParLe
  gen c, t, a
  c.add opr
  gen c, t, b
  c.add ParRi

template binaryop(opr) =
  let (typ, a) = sons2(t, n)
  c.add ParLe
  c.add ParLe
  gen c, t, typ
  c.add ParRi
  c.add opr
  gen c, t, a
  c.add ParRi

template checkedBinaryop(opr) =
  let (typ, labIdx, a, b) = sons4(t, n)
  let bits = integralBits(c.m.types[t[typ].typeId])
  let lab = t[labIdx].label

  c.add (opr & $bits)
  c.add ParLe
  c.gen t, a
  c.add Comma
  c.gen t, b
  c.add Comma
  c.add "L" & $lab.int
  c.add ParRi

proc genNumberConv(c: var GeneratedCode; t: Tree; n: NodePos) =
  let (typ, arg) = sons2(t, n)
  if t[arg].kind == IntVal:
    let litId = t[arg].litId
    c.add ParLe
    c.add ParLe
    gen c, t, typ
    c.add ParRi
    case c.m.types[t[typ].typeId].kind
    of UIntTy:
      let x = cast[uint64](c.m.lit.numbers[litId])
      c.add $x
    of FloatTy:
      let x = cast[float64](c.m.lit.numbers[litId])
      c.add $x
    else:
      gen c, t, arg
    c.add ParRi
  else:
    binaryop ""

template moveToDataSection(body: untyped) =
  let oldLen = c.code.len
  body
  for i in oldLen ..< c.code.len:
    c.data.add c.code[i]
  setLen c.code, oldLen

proc gen(c: var GeneratedCode; t: Tree; n: NodePos) =
  case t[n].kind
  of Nop:
    discard "nothing to emit"
  of ImmediateVal:
    c.add $t[n].immediateVal
  of IntVal:
    genIntLit c, c.m.lit, t[n].litId
  of StrVal:
    c.code.add genStrLit(c, c.m.lit, t[n].litId)
  of Typed:
    genType c, c.m.types, c.m.lit, t[n].typeId
  of SymDef, SymUse:
    let s = t[n].symId
    if c.needsPrefix.contains(s.int):
      c.code.add mangleModuleName(c, c.m.namespace)
      c.add "__"
      c.add $s
    else:
      # XXX Use proper names here
      c.add "q"
      c.add $s

  of ModuleSymUse:
    let (x, y) = sons2(t, n)
    let u = mangleModuleName(c, t[x].litId)
    let s = t[y].immediateVal
    c.code.add u
    c.add "__"
    c.add $s

  of NilVal:
    c.add NullPtr
  of LoopLabel:
    c.add WhileKeyword
    c.add ParLe
    c.add "1"
    c.add ParRi
    c.add CurlyLe
  of GotoLoop:
    c.add CurlyRi
  of Label:
    let lab = t[n].label
    c.add "L"
    c.add $lab.int
    c.add Colon
    c.add Semicolon
  of Goto:
    let lab = t[n].label
    c.add "goto L"
    c.add $lab.int
    c.add Semicolon
  of CheckedGoto:
    discard "XXX todo"
  of ArrayConstr:
    c.add CurlyLe
    c.add ".a = "
    c.add CurlyLe
    var i = 0
    for ch in sonsFrom1(t, n):
      if i > 0: c.add Comma
      c.gen t, ch
      inc i
    c.add CurlyRi
    c.add CurlyRi
  of ObjConstr:
    c.add CurlyLe
    var i = 0
    for ch in sonsFrom1(t, n):
      if i mod 2 == 0:
        if i > 0: c.add Comma
        c.add ".F" & $t[ch].immediateVal
        c.add AsgnOpr
      else:
        c.gen t, ch
      inc i
    c.add CurlyRi
  of Ret:
    c.add ReturnKeyword
    c.gen t, n.firstSon
    c.add Semicolon
  of Select:
    c.add SwitchKeyword
    c.add ParLe
    let (_, selector) = sons2(t, n)
    c.gen t, selector
    c.add ParRi
    c.add CurlyLe
    for ch in sonsFromN(t, n, 2):
      c.gen t, ch
    c.add CurlyRi
  of SelectPair:
    let (le, ri) = sons2(t, n)
    c.gen t, le
    c.gen t, ri
  of SelectList:
    for ch in sons(t, n):
      c.gen t, ch
  of SelectValue:
    c.add CaseKeyword
    c.gen t, n.firstSon
    c.add Colon
  of SelectRange:
    let (le, ri) = sons2(t, n)
    c.add CaseKeyword
    c.gen t, le
    c.add " ... "
    c.gen t, ri
    c.add Colon
  of ForeignDecl:
    c.data.add Token(ExternKeyword)
    c.gen t, n.firstSon
  of SummonGlobal:
    moveToDataSection:
      let (typ, sym) = sons2(t, n)
      c.genGlobal t, sym, typ, ""
      c.add Semicolon
  of SummonThreadLocal:
    moveToDataSection:
      let (typ, sym) = sons2(t, n)
      c.genGlobal t, sym, typ, "__thread "
      c.add Semicolon
  of SummonConst:
    moveToDataSection:
      let (typ, sym, val) = sons3(t, n)
      c.genGlobal t, sym, typ, "const "
      c.add AsgnOpr
      c.gen t, val
      c.add Semicolon
  of Summon, SummonResult:
    let (typ, sym) = sons2(t, n)
    c.genLocal t, sym, typ, ""
    c.add Semicolon

  of SummonParam:
    raiseAssert "SummonParam should have been handled in genProc"
  of Kill:
    discard "we don't care about Kill instructions"
  of AddrOf:
    let (_, arg) = sons2(t, n)
    c.add "&"
    gen c, t, arg
  of DerefArrayAt:
    let (_, a, i) = sons3(t, n)
    gen c, t, a
    c.add BracketLe
    gen c, t, i
    c.add BracketRi
  of ArrayAt:
    let (_, a, i) = sons3(t, n)
    gen c, t, a
    c.add Dot
    c.add "a"
    c.add BracketLe
    gen c, t, i
    c.add BracketRi
  of FieldAt:
    let (_, a, b) = sons3(t, n)
    gen c, t, a
    let field = t[b].immediateVal
    c.add Dot
    c.add "F" & $field
  of DerefFieldAt:
    let (_, a, b) = sons3(t, n)
    gen c, t, a
    let field = t[b].immediateVal
    c.add Arrow
    c.add "F" & $field
  of Load:
    let (_, arg) = sons2(t, n)
    c.add ParLe
    c.add "*"
    gen c, t, arg
    c.add ParRi
  of Store:
    raiseAssert "Assumption was that Store is unused!"
  of Asgn:
    let (_, dest, src) = sons3(t, n)
    gen c, t, dest
    c.add AsgnOpr
    gen c, t, src
    c.add Semicolon
  of CheckedRange:
    c.add "nimCheckRange"
    c.add ParLe
    let (_, gotoInstr, x, a, b) = sons5(t, n)
    gen c, t, x
    c.add Comma
    gen c, t, a
    c.add Comma
    gen c, t, b
    c.add Comma
    c.add "L" & $t[gotoInstr].label.int
    c.add ParRi
  of CheckedIndex:
    c.add "nimCheckIndex"
    c.add ParLe
    let (gotoInstr, x, a) = sons3(t, n)
    gen c, t, x
    c.add Comma
    gen c, t, a
    c.add Comma
    c.add "L" & $t[gotoInstr].label.int
    c.add ParRi
  of Call, IndirectCall:
    let (typ, fn) = sons2(t, n)
    gen c, t, fn
    c.add ParLe
    var i = 0
    for ch in sonsFromN(t, n, 2):
      if i > 0: c.add Comma
      gen c, t, ch
      inc i
    c.add ParRi
    if c.m.types[t[typ].typeId].kind == VoidTy:
      c.add Semicolon
  of CheckedCall, CheckedIndirectCall:
    let (typ, gotoInstr, fn) = sons3(t, n)
    gen c, t, fn
    c.add ParLe
    var i = 0
    for ch in sonsFromN(t, n, 3):
      if i > 0: c.add Comma
      gen c, t, ch
      inc i
    c.add ParRi
    if c.m.types[t[typ].typeId].kind == VoidTy:
      c.add Semicolon

  of CheckedAdd: checkedBinaryop "nimAddInt"
  of CheckedSub: checkedBinaryop "nimSubInt"
  of CheckedMul: checkedBinaryop "nimMulInt"
  of CheckedDiv: checkedBinaryop "nimDivInt"
  of CheckedMod: checkedBinaryop "nimModInt"
  of Add: triop " + "
  of Sub: triop " - "
  of Mul: triop " * "
  of Div: triop " / "
  of Mod: triop " % "
  of BitShl: triop " << "
  of BitShr: triop " >> "
  of BitAnd: triop " & "
  of BitOr: triop " | "
  of BitXor: triop " ^ "
  of BitNot: binaryop " ~ "
  of BoolNot: binaryop " !"
  of Eq: cmpop " == "
  of Le: cmpop " <= "
  of Lt: cmpop " < "
  of Cast: binaryop ""
  of NumberConv: genNumberConv c, t, n
  of CheckedObjConv: binaryop ""
  of ObjConv: binaryop ""
  of Emit: raiseAssert "cannot interpret: Emit"
  of ProcDecl: genProcDecl c, t, n, false
  of ForeignProcDecl: genProcDecl c, t, n, true
  of PragmaPair, PragmaId, TestOf, Yld, SetExc, TestExc:
    c.add "cannot interpret: " & $t[n].kind

const
  Prelude = """
/* GENERATED CODE. DO NOT EDIT. */

#ifdef __cplusplus
#define NB8 bool
#elif (defined(__STDC_VERSION__) && __STDC_VERSION__ >= 199901)
// see #13798: to avoid conflicts for code emitting `#include <stdbool.h>`
#define NB8 _Bool
#else
typedef unsigned char NB8; // best effort
#endif

typedef unsigned char NC8;

typedef float NF32;
typedef double NF64;
#if defined(__BORLANDC__) || defined(_MSC_VER)
typedef signed char NI8;
typedef signed short int NI16;
typedef signed int NI32;
typedef __int64 NI64;
/* XXX: Float128? */
typedef unsigned char NU8;
typedef unsigned short int NU16;
typedef unsigned int NU32;
typedef unsigned __int64 NU64;
#elif defined(HAVE_STDINT_H)
#ifndef USE_NIM_NAMESPACE
#  include <stdint.h>
#endif
typedef int8_t NI8;
typedef int16_t NI16;
typedef int32_t NI32;
typedef int64_t NI64;
typedef uint8_t NU8;
typedef uint16_t NU16;
typedef uint32_t NU32;
typedef uint64_t NU64;
#elif defined(HAVE_CSTDINT)
#ifndef USE_NIM_NAMESPACE
#  include <cstdint>
#endif
typedef std::int8_t NI8;
typedef std::int16_t NI16;
typedef std::int32_t NI32;
typedef std::int64_t NI64;
typedef std::uint8_t NU8;
typedef std::uint16_t NU16;
typedef std::uint32_t NU32;
typedef std::uint64_t NU64;
#else
/* Unknown compiler/version, do our best */
#ifdef __INT8_TYPE__
typedef __INT8_TYPE__ NI8;
#else
typedef signed char NI8;
#endif
#ifdef __INT16_TYPE__
typedef __INT16_TYPE__ NI16;
#else
typedef signed short int NI16;
#endif
#ifdef __INT32_TYPE__
typedef __INT32_TYPE__ NI32;
#else
typedef signed int NI32;
#endif
#ifdef __INT64_TYPE__
typedef __INT64_TYPE__ NI64;
#else
typedef long long int NI64;
#endif
/* XXX: Float128? */
#ifdef __UINT8_TYPE__
typedef __UINT8_TYPE__ NU8;
#else
typedef unsigned char NU8;
#endif
#ifdef __UINT16_TYPE__
typedef __UINT16_TYPE__ NU16;
#else
typedef unsigned short int NU16;
#endif
#ifdef __UINT32_TYPE__
typedef __UINT32_TYPE__ NU32;
#else
typedef unsigned int NU32;
#endif
#ifdef __UINT64_TYPE__
typedef __UINT64_TYPE__ NU64;
#else
typedef unsigned long long int NU64;
#endif
#endif

#ifdef NIM_INTBITS
#  if NIM_INTBITS == 64
typedef NI64 NI;
typedef NU64 NU;
#  elif NIM_INTBITS == 32
typedef NI32 NI;
typedef NU32 NU;
#  elif NIM_INTBITS == 16
typedef NI16 NI;
typedef NU16 NU;
#  elif NIM_INTBITS == 8
typedef NI8 NI;
typedef NU8 NU;
#  else
#    error "invalid bit width for int"
#  endif
#endif

#define NIM_STRLIT_FLAG ((NU)(1) << ((NIM_INTBITS) - 2)) /* This has to be the same as system.strlitFlag! */

#define nimAddInt64(a, b, L) ({long long int res; if(__builtin_saddll_overflow(a, b, &res)) goto L; res})
#define nimSubInt64(a, b, L) ({long long int res; if(__builtin_ssubll_overflow(a, b, &res)) goto L; res})
#define nimMulInt64(a, b, L) ({long long int res; if(__builtin_smulll_overflow(a, b, &res)) goto L; res})

#define nimAddInt32(a, b, L) ({long int res; if(__builtin_sadd_overflow(a, b, &res)) goto L; res})
#define nimSubInt32(a, b, L) ({long int res; if(__builtin_ssub_overflow(a, b, &res)) goto L; res})
#define nimMulInt32(a, b, L) ({long int res; if(__builtin_smul_overflow(a, b, &res)) goto L; res})

#define nimCheckRange(x, a, b, L) ({if (x < a || x > b) goto L; x})
#define nimCheckIndex(x, a, L) ({if (x >= a) goto L; x})

"""

proc traverseCode(c: var GeneratedCode) =
  const AllowedInToplevelC = {SummonConst, SummonGlobal, SummonThreadLocal,
                              ProcDecl, ForeignDecl, ForeignProcDecl}
  var i = NodePos(0)
  while i.int < c.m.code.len:
    let oldLen = c.code.len
    let moveToInitSection = c.m.code[NodePos(i)].kind notin AllowedInToplevelC

    gen c, c.m.code, NodePos(i)
    next c.m.code, i

    if moveToInitSection:
      for i in oldLen ..< c.code.len:
        c.init.add c.code[i]
      setLen c.code, oldLen

proc generateCode*(inp, outp: string) =
  var c = initGeneratedCode(load(inp))

  var co = TypeOrder()
  traverseTypes(c.m, co)

  generateTypes(c, c.m.types, c.m.lit, co)
  let typeDecls = move c.code

  traverseCode c
  var f = CppFile(f: open(outp, fmWrite))
  f.write "#define NIM_INTBITS " & $c.m.intbits & "\n"
  f.write Prelude
  writeTokenSeq f, c.includes, c
  writeTokenSeq f, typeDecls, c
  writeTokenSeq f, c.data, c
  writeTokenSeq f, c.protos, c
  writeTokenSeq f, c.code, c
  if c.init.len > 0:
    f.write "void __attribute__((constructor)) init(void) {"
    writeTokenSeq f, c.init, c
    f.write "}\n\n"
  f.f.close
