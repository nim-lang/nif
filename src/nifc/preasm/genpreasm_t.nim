#
#
#           NIFC Compiler
#        (c) Copyright 2024 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# included from genpreasm.nim

## Generates PreASM types from NIFC types.

proc align(address, alignment: int): int =
  result = (address + (alignment - 1)) and not (alignment - 1)

proc mergeBranch(arg: var AsmSlot; value: AsmSlot) =
  arg.offset = max(arg.offset, value.offset)
  arg.align = max(arg.align, value.align)

type
  TypeList = object
    processed: IntSet
    s: seq[TypeId]

proc add(dest: var TypeList; elem: TypeId) =
  if not containsOrIncl(dest.processed, int(elem)):
    dest.s.add elem

type
  TypeOrder = object
    ordered: TypeList
    lookedAt, lookedAtBodies: IntSet

proc traverseObjectBody(m: Module; o: var TypeOrder; t: TypeId)

proc recordDependency(m: Module; o: var TypeOrder; parent, child: TypeId) =
  var ch = child
  var viaPointer = false
  while true:
    case m.code[ch].kind
    of APtrC, PtrC:
      viaPointer = true
      ch = elementType(m.code, ch)
    of FlexarrayC:
      ch = elementType(m.code, ch)
    else:
      break

  case m.code[ch].kind
  of ObjectC, UnionC:
    let obj = ch
    if viaPointer:
      discard "we know the size of a pointer anyway"
    else:
      if not containsOrIncl(o.lookedAt, obj.int):
        traverseObjectBody(m, o, obj)
      o.ordered.add tracebackTypeC(m, ch)
  of ArrayC:
    if viaPointer:
      discard "we know the size of a pointer anyway"
    else:
      if not containsOrIncl(o.lookedAt, ch.int):
        traverseObjectBody(m, o, ch)
      o.ordered.add tracebackTypeC(m, ch)
  of Sym:
    # follow the symbol to its definition:
    let id = m.code[ch].litId
    let def = m.defs.getOrDefault(id)
    if def == NodePos(0):
      error m, "undeclared symbol: ", m.code, ch
    else:
      let decl = asTypeDecl(m.code, def)
      if not containsOrIncl(o.lookedAtBodies, decl.body.int):
        recordDependency m, o, parent, decl.body
  else:
    discard "uninteresting type as we only focus on the required struct declarations"

proc traverseObjectBody(m: Module; o: var TypeOrder; t: TypeId) =
  for x in sons(m.code, t):
    case m.code[x].kind
    of FldC:
      let decl = asFieldDecl(m.code, x)
      recordDependency m, o, t, decl.typ
    of Sym:
      # inheritance
      recordDependency m, o, t, x
    else: discard

proc traverseTypes(m: Module; o: var TypeOrder) =
  for ch in m.types:
    let decl = asTypeDecl(m.code, ch)
    let t = decl.body
    case m.code[t].kind
    of ObjectC:
      traverseObjectBody m, o, t
    of UnionC:
      traverseObjectBody m, o, t
    of ArrayC:
      traverseObjectBody m, o, t
    of ProctypeC:
      o.ordered.add ch
    of EnumC:
      # (efld SymbolDef Expr)
      # EnumDecl ::= (enum Type EnumFieldDecl+)
      o.ordered.add ch
    else: discard

template integralBits(c: GeneratedCode; types: TypeGraph; t: TypeId): int =
  let lit = types[t.firstSon].litId
  let r = c.m.lits.strings[lit]
  let res = parseBiggestInt(r)
  if res == -1:
    c.intmSize
  else: # 8, 16, 32, 64 etc.
    res

proc genWas(c: var GeneratedCode; t: Tree; ch: NodePos) =
  c.code.buildTree(WasT, t[ch].info):
    c.code.add toToken(Ident, pool.strings.getOrIncl(toString(t, ch.firstSon, c.m)), t[ch].info)

proc genFieldPragmas(c: var GeneratedCode; types: TypeGraph; n: NodePos;
                     field: var AsmSlot; bits: var string) =
  # CommonPragma ::= (align Number) | (was Identifier) | Attribute
  # FieldPragma ::= CommonPragma | (bits Number)
  if types[n].kind == Empty:
    c.addEmpty types[n].info
  elif types[n].kind == PragmasC:
    for ch in sons(types, n):
      case types[ch].kind
      of AlignC:
        field.align = parseInt(c.m.lits.strings[types[ch.firstSon].litId])
      of WasC:
        genWas c, types, ch
      of AttrC:
        discard "ignore attributes"
      of BitsC:
        error c.m, "bit sizes fields are not supported: ", types, ch
      else:
        error c.m, "invalid proc type pragma: ", types, ch
  else:
    error c.m, "expected field pragmas but got: ", types, n

proc fieldName(c: var GeneratedCode; tree: TypeGraph; n: NodePos): LitId =
  if tree[n].kind in {Sym, SymDef}:
    result = tree[n].litId
  else:
    error c.m, "field name must be a SymDef, but got: ", tree, n
    result = LitId(0)

proc setField(c: var GeneratedCode; name: LitId; obj: AsmSlot; t: var AsmSlot) =
  t.offset = obj.size + (obj.size mod t.align)
  c.fields[name] = t

proc fillTypeSlot(c: var GeneratedCode; types: TypeGraph; t: TypeId; dest: var AsmSlot)

proc genObjectBody(c: var GeneratedCode; types: TypeGraph; n: NodePos;
                          obj: var AsmSlot; k: NifcKind) =
  obj.kind = AMem
  for x in sons(types, n):
    case types[x].kind
    of FldC:
      let decl = asFieldDecl(types, x)
      let fn = fieldName(c, types, decl.name)
      var bits = ""
      var f = AsmSlot()
      genFieldPragmas c, types, decl.pragmas, f, bits
      fillTypeSlot c, types, decl.typ, f
      setField c, fn, obj, f
      if k == ObjectC:
        inc obj.size, f.size
      else:
        # union:
        obj.size = max(obj.size, f.size)
      obj.align = max(obj.align, f.align)
    of Sym:
      fillTypeSlot c, types, x, obj
    else: discard
  # padding at object end:
  obj.size = obj.size + (obj.size mod obj.align)

proc fillTypeSlot(c: var GeneratedCode; types: TypeGraph; t: TypeId; dest: var AsmSlot) =
  let k = types[t].kind
  case k
  of VoidC:
    error c.m, "internal error: Cannot handle 'void' type: ", types, t
  of IntC:
    let bytes = integralBits(c, types, t) div 8
    dest = AsmSlot(kind: AInt, size: bytes, align: bytes)
  of UIntC, CharC:
    let bytes = integralBits(c, types, t) div 8
    dest = AsmSlot(kind: AUInt, size: bytes, align: bytes)
  of FloatC:
    let bytes = integralBits(c, types, t) div 8
    dest = AsmSlot(kind: AFloat, size: bytes, align: bytes)
  of BoolC:
    dest = AsmSlot(kind: ABool, size: 1, align: 1)
  of Sym:
    let id = types[t].litId
    let def = c.m.defs.getOrDefault(id)
    if def == NodePos(0):
      error c.m, "undeclared symbol: ", c.m.code, t
    else:
      if c.types.hasKey(id):
        dest = c.types[id]
      else:
        let decl = asTypeDecl(c.m.code, def)
        fillTypeSlot c, c.m.code, decl.body, dest
        c.types[id] = dest
  of PtrC, APtrC, ProctypeC:
    dest = AsmSlot(kind: AUInt, size: c.intmSize, align: c.intmSize)
  of FlexarrayC:
    # Call `elementType` to get the alignment right:
    fillTypeSlot c, types, elementType(types, t), dest
    dest.kind = AMem
    dest.size = 0
  of EnumC:
    let baseType = t.firstSon
    fillTypeSlot c, types, baseType, dest
  of ArrayC:
    let (elem, size) = sons2(types, t)
    fillTypeSlot c, types, elem, dest
    dest.kind = AMem
    dest.size *= parseInt(c.m.lits.strings[types[size].litId])
  of ObjectC, UnionC:
    genObjectBody c, types, t, dest, k
  else:
    error c.m, "node is not a type: ", types, t

proc generateTypes(c: var GeneratedCode; types: TypeGraph; o: TypeOrder) =
  for d in o.ordered.s:
    let decl = asTypeDecl(types, d)
    let litId = types[decl.name].litId
    if not c.generatedTypes.containsOrIncl(litId.int):
      var t = AsmSlot()
      fillTypeSlot c, types, decl.body, t
      c.types[litId] = t

proc genType(c: var GeneratedCode; types: TypeGraph; t: TypeId; alignOverride = -1) =
  var dest = AsmSlot()
  fillTypeSlot c, types, t, dest
  if alignOverride >= 0:
    dest.align = alignOverride
  let tag =
    case dest.kind
    of ABool: BT
    of AInt: IT
    of AUInt: UT
    of AFloat: FT
    of AMem: MT

  let info = types[t].info
  c.buildTree tag, info:
    if tag != BT:
      c.genIntLit dest.size, info
      if dest.align != dest.size:
        c.genIntLit dest.align, info
