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
      error m, "undeclared symbol: ", m.types, ch
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

template integralBits(types: TypeGraph; t: TypeId): string =
  let lit = types[t.firstSon].litId
  g.m.lits.strings[lit]

proc genProcTypePragma(g: var GeneratedCode; types: TypeGraph; n: NodePos; isVarargs: var bool) =
  # ProcTypePragma ::= CallingConvention | (varargs) | Attribute
  case types[n].kind
  of CallingConventions:
    g.add " __" & $types[n].kind
  of VarargsC:
    isVarargs = true
  of AttrC:
    g.add " __attribute__((" & toString(types, n.firstSon, g.m) & "))"
  else:
    error g.m, "invalid proc type pragma: ", types, n

proc genProcTypePragmas(g: var GeneratedCode; types: TypeGraph; n: NodePos; isVarargs: var bool) =
  if types[n].kind == Empty: return
  if types[n].kind == PragmasC:
    for ch in sons(types, n):
      genProcTypePragma(g, types, ch, isVarargs)
  else:
    error g.m, "expected proc type pragmas but got: ", types, n

proc genFieldPragmas(g: var GeneratedCode; types: TypeGraph; n: NodePos; bits: var string) =
  # CommonPragma ::= (align Number) | (was Identifier) | Attribute
  # FieldPragma ::= CommonPragma | (bits Number)
  if types[n].kind == Empty: return
  if types[n].kind == PragmasC:
    for ch in sons(types, n):
      case types[ch].kind
      of AlignC:
        g.add " NIM_ALIGN(" & toString(types, ch.firstSon, g.m) & ")"
      of WasC:
        g.add "/* " & toString(types, ch.firstSon, g.m) & " */"
      of AttrC:
        g.add " __attribute__((" & toString(types, ch.firstSon, g.m) & "))"
      of BitsC:
        bits = toString(types, ch.firstSon, g.m)
      else:
        error g.m, "invalid proc type pragma: ", types, ch
  else:
    error g.m, "expected field pragmas but got: ", types, n

proc genType(g: var GeneratedCode; types: TypeGraph; t: TypeId; name = "") =
  template maybeAddName =
    if name != "":
      g.add Space
      g.add name

  template atom(s: string) =
    g.add s
    maybeAddName()
  case types[t].kind
  of VoidC: atom "void"
  of IntC: atom "NI" & types.integralBits(t)
  of UIntC: atom "NU" & types.integralBits(t)
  of FloatC: atom "NF" & types.integralBits(t)
  of BoolC: atom "NB" & types.integralBits(t)
  of CharC: atom "NC" & types.integralBits(t)
  of Sym:
    atom g.m.lits.strings[types[t].litId]
  of PtrC, APtrC:
    # XXX implement `ro` etc annotations
    genType g, types, elementType(types, t)
    g.add Star
    maybeAddName()
  of FlexarrayC:
    genType g, types, elementType(types, t)
    maybeAddName()
    g.add BracketLe
    g.add BracketRi
  of ProctypeC:
    let decl = asProcType(types, t)
    genType g, types, decl.returnType
    g.add Space
    g.add ParLe
    var isVarargs = false
    genProcTypePragmas g, types, decl.pragmas, isVarargs
    g.add Star # "(*fn)"
    maybeAddName()
    g.add ParRi
    g.add ParLe
    var i = 0
    for ch in sons(types, decl.params):
      if i > 0: g.add Comma
      genType g, types, ch
      inc i
    if isVarargs:
      if i > 0: g.add Comma
      g.add "..."
    if i == 0:
      g.add "void"
    g.add ParRi
  else:
    error g.m, "node is not a type: ", types, t

proc mangleField(g: var GeneratedCode; tree: TypeGraph; n: NodePos): string =
  if tree[n].kind in {Sym, SymDef}:
    result = mangle(g.m.lits.strings[tree[n].litId])
  else:
    error g.m, "field name must be a SymDef, but got: ", tree, n
    result = "InvalidFieldName"

proc genObjectOrUnionBody(g: var GeneratedCode; types: TypeGraph; n: NodePos) =
  for x in sons(types, n):
    case types[x].kind
    of FldC:
      let decl = asFieldDecl(types, x)
      let f = mangleField(g, types, decl.name)
      var bits = ""
      genFieldPragmas g, types, decl.pragmas, bits
      genType g, types, decl.typ, f
      if bits.len > 0:
        g.add " : "
        g.add bits
      g.add Semicolon
    of Sym:
      genType g, types, x, "Q"
      g.add Semicolon
    else: discard

proc generateTypes(g: var GeneratedCode; types: TypeGraph; c: TypeOrder) =
  for (d, declKeyword) in c.forwardedDecls.s:
    let decl = asTypeDecl(types, d)
    let s {.cursor.} = g.m.lits.strings[types[decl.name].litId]
    g.add declKeyword
    g.add s
    g.add Space
    g.add s
    g.add Semicolon

  for (d, declKeyword) in c.ordered.s:
    let decl = asTypeDecl(types, d)
    let litId = types[decl.name].litId
    if not g.generatedTypes.containsOrIncl(litId.int):
      let s {.cursor.} = g.m.lits.strings[litId]
      g.add declKeyword
      g.add CurlyLe
      case types[decl.body].kind
      of ArrayC:
        let (elem, size) = sons2(types, decl.body)
        genType g, types, elem, "a"
        g.add BracketLe
        g.genIntLit types[size].litId
        g.add BracketRi
        g.add Semicolon
      of EnumC:
        assert false, "too implement"
      else:
        # XXX generate attributes and pragmas here
        g.genObjectOrUnionBody types, decl.body
      g.add CurlyRi
      g.add s
      g.add Semicolon

