#
#
#           NIFC Compiler
#        (c) Copyright 2024 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# included from codegen.nim

## Generates C types from NIFC types.

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

proc traverseObjectBody(m: Module; o: var TypeOrder; t: TypeId)

proc recordDependency(m: Module; o: var TypeOrder; parent, child: TypeId) =
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
      o.forwardedDecls.add parent, decl
    else:
      if not containsOrIncl(o.lookedAt, obj.int):
        traverseObjectBody(m, o, obj)
      o.ordered.add obj, decl
  of ArrayC:
    if viaPointer:
      o.forwardedDecls.add parent, TypedefStruct
    else:
      if not containsOrIncl(o.lookedAt, ch.int):
        traverseObjectBody(m, o, ch)
      o.ordered.add ch, TypedefStruct
  of Sym:
    # follow the symbol to its definition:
    let id = m.types[ch].litId
    let def = m.defs.getOrDefault(id)
    if def == NodePos(0):
      error m, "undeclared symbol: ", m.types, ch
    else:
      let decl = asTypeDecl(m.types, def)
      if not containsOrIncl(o.lookedAtBodies, decl.body.int):
        recordDependency m, o, parent, decl.body
  else:
    discard "uninteresting type as we only focus on the required struct declarations"

proc traverseObjectBody(m: Module; o: var TypeOrder; t: TypeId) =
  for x in sons(m.types, t):
    case m.types[x].kind
    of FldC:
      let decl = asFieldDecl(m.types, x)
      recordDependency m, o, t, decl.typ
    of Sym:
      # inheritance
      recordDependency m, o, t, x
    else: discard

proc traverseTypes(m: Module; o: var TypeOrder) =
  for ch in sons(m.types, StartPos):
    let decl = asTypeDecl(m.types, ch)
    let t = decl.body
    case m.types[t].kind
    of ObjectC:
      traverseObjectBody m, o, t
      o.ordered.add ch, TypedefStruct
    of UnionC:
      traverseObjectBody m, o, t
      o.ordered.add ch, TypedefUnion
    of ArrayC:
      traverseObjectBody m, o, t
      o.ordered.add ch, TypedefStruct
    of ProctypeC:
      # XXX
      #traverseProctypeBody m, o, t
      o.ordered.add ch, TypedefKeyword
    of EnumC:
      o.ordered.add ch, TypedefKeyword
    else: discard

template integralBits(types: TypeGraph; t: TypeId): string =
  let lit = types[t.firstSon].litId
  let r = c.m.lits.strings[lit]
  (if r == "M": "" else: r)

proc genProcTypePragma(c: var GeneratedCode; types: TypeGraph; n: NodePos; isVarargs: var bool) =
  # ProcTypePragma ::= CallingConvention | (varargs) | Attribute
  case types[n].kind
  of CallingConventions:
    c.add " __" & $types[n].kind
  of VarargsC:
    isVarargs = true
  of AttrC:
    c.add " __attribute__((" & toString(types, n.firstSon, c.m) & "))"
  else:
    error c.m, "invalid proc type pragma: ", types, n

proc genProcTypePragmas(c: var GeneratedCode; types: TypeGraph; n: NodePos; isVarargs: var bool) =
  if types[n].kind == Empty: return
  if types[n].kind == PragmasC:
    for ch in sons(types, n):
      genProcTypePragma(c, types, ch, isVarargs)
  else:
    error c.m, "expected proc type pragmas but got: ", types, n

proc genFieldPragmas(c: var GeneratedCode; types: TypeGraph; n: NodePos; bits: var string) =
  # CommonPragma ::= (align Number) | (was Identifier) | Attribute
  # FieldPragma ::= CommonPragma | (bits Number)
  if types[n].kind == Empty: return
  if types[n].kind == PragmasC:
    for ch in sons(types, n):
      case types[ch].kind
      of AlignC:
        c.add " NIM_ALIGN(" & toString(types, ch.firstSon, c.m) & ")"
      of WasC:
        c.add "/* " & toString(types, ch.firstSon, c.m) & " */"
      of AttrC:
        c.add " __attribute__((" & toString(types, ch.firstSon, c.m) & "))"
      of BitsC:
        bits = toString(types, ch.firstSon, c.m)
      else:
        error c.m, "invalid proc type pragma: ", types, ch
  else:
    error c.m, "expected field pragmas but got: ", types, n

proc genType(c: var GeneratedCode; types: TypeGraph; t: TypeId; name = "") =
  template maybeAddName =
    if name != "":
      c.add Space
      c.add name

  template atom(s: string) =
    c.add s
    maybeAddName()
  case types[t].kind
  of VoidC: atom "void"
  of IntC: atom "NI" & types.integralBits(t)
  of UIntC: atom "NU" & types.integralBits(t)
  of FloatC: atom "NF" & types.integralBits(t)
  of BoolC: atom "NB" & types.integralBits(t)
  of CharC: atom "NC" & types.integralBits(t)
  of Sym:
    atom mangle(c.m.lits.strings[types[t].litId])
  of PtrC, APtrC:
    # XXX implement `ro` etc annotations
    genType c, types, elementType(types, t)
    c.add Star
    maybeAddName()
  of FlexarrayC:
    genType c, types, elementType(types, t)
    maybeAddName()
    c.add BracketLe
    c.add BracketRi
  of ProctypeC:
    let decl = asProcType(types, t)
    genType c, types, decl.returnType
    c.add Space
    c.add ParLe
    var isVarargs = false
    genProcTypePragmas c, types, decl.pragmas, isVarargs
    c.add Star # "(*fn)"
    maybeAddName()
    c.add ParRi
    c.add ParLe
    var i = 0
    for ch in sons(types, decl.params):
      if i > 0: c.add Comma
      genType c, types, ch
      inc i
    if isVarargs:
      if i > 0: c.add Comma
      c.add "..."
    if i == 0:
      c.add "void"
    c.add ParRi
  else:
    error c.m, "node is not a type: ", types, t

proc mangleField(c: var GeneratedCode; tree: TypeGraph; n: NodePos): string =
  if tree[n].kind in {Sym, SymDef}:
    result = mangle(c.m.lits.strings[tree[n].litId])
  else:
    error c.m, "field name must be a SymDef, but got: ", tree, n
    result = "InvalidFieldName"

proc genObjectOrUnionBody(c: var GeneratedCode; types: TypeGraph; n: NodePos) =
  for x in sons(types, n):
    case types[x].kind
    of FldC:
      let decl = asFieldDecl(types, x)
      let f = mangleField(c, types, decl.name)
      var bits = ""
      genFieldPragmas c, types, decl.pragmas, bits
      genType c, types, decl.typ, f
      if bits.len > 0:
        c.add " : "
        c.add bits
      c.add Semicolon
    of Sym:
      genType c, types, x, "Q"
      c.add Semicolon
    else: discard

proc genEnumDecl(c: var GeneratedCode; t: TypeGraph; n: NodePos) =
  # (efld SymbolDef Expr)
  # EnumDecl ::= (enum Type EnumFieldDecl+)
  let baseType = n.firstSon
  for ch in sonsFromX(t, n):
    if t[ch].kind == EfldC:
      let (a, b) = sons2(t, ch)
      if t[a].kind == SymDef:
        let enumFieldName = mangle(c.m.lits.strings[t[a].litId])
        c.add "#define "
        c.add enumFieldName
        c.add Space
        c.add ParLe
        c.add ParLe
        c.genType t, baseType
        c.add ParRi
        case t[b].kind
        of IntLit: c.genIntLit t[b].litId
        of UIntLit: c.genUIntLit t[b].litId
        else:
          error c.m, "expected `Number` but got: ", t, a
        c.add ParRi
        c.add NewLine
      else:
        error c.m, "expected `SymbolDef` but got: ", t, a
    else:
      error c.m, "expected `efld` but got: ", t, ch

proc generateTypes(c: var GeneratedCode; types: TypeGraph; o: TypeOrder) =
  for (d, declKeyword) in o.forwardedDecls.s:
    let decl = asTypeDecl(types, d)
    let s = mangle(c.m.lits.strings[types[decl.name].litId])
    c.add declKeyword
    c.add s
    c.add Space
    c.add s
    c.add Semicolon

  for (d, declKeyword) in o.ordered.s:
    let decl = asTypeDecl(types, d)
    let litId = types[decl.name].litId
    if not c.generatedTypes.containsOrIncl(litId.int):
      let s = mangle(c.m.lits.strings[litId])
      case types[decl.body].kind
      of ArrayC:
        c.add declKeyword
        c.add CurlyLe
        let (elem, size) = sons2(types, decl.body)
        genType c, types, elem, "a"
        c.add BracketLe
        c.genIntLit types[size].litId
        c.add BracketRi
        c.add Semicolon
        c.add CurlyRi
        c.add s
        c.add Semicolon
      of EnumC:
        genEnumDecl c, types, decl.body
      of ProctypeC:
        c.add TypedefKeyword
        genType c, types, decl.body, s
        c.add Semicolon
      else:
        c.add declKeyword
        c.add CurlyLe
        # XXX generate attributes and pragmas here
        c.genObjectOrUnionBody types, decl.body
        c.add CurlyRi
        c.add s
        c.add Semicolon
