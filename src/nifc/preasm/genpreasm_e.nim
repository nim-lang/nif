#
#
#           NIFC Compiler
#        (c) Copyright 2024 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# included from genpreasm.nim

type
  XMode = enum
    WantValue, WantAddr

proc genx(c: var GeneratedCode; t: Tree; n: NodePos; mode: XMode)

template typedBinOp(opr) {.dirty.} =
  let (typ, a, b) = sons3(t, n)
  c.buildTree opr, info:
    genType c, typ
    genx c, t, a, WantValue
    genx c, t, b, WantValue

template cmpOp(opr) {.dirty.} =
  c.buildTree opr, info:
    let (a, b) = sons2(t, n)
    genTypeof c, a
    genx c, t, a, WantValue
    genx c, t, b, WantValue

template unOp(opr) {.dirty.} =
  c.buildTree opr, info:
    genTypeof c, n.firstSon
    genx c, t, n.firstSon, WantValue

template typedUnOp(opr) {.dirty.} =
  let (typ, a) = sons2(t, n)
  c.buildTree opr, info:
    genType c, typ
    genx c, t, a, WantValue

proc genCall(c: var GeneratedCode; t: Tree; n: NodePos) =
  c.buildTree CallT, t[n].info:
    for ch in sons(t, n):
      genx c, t, ch, WantValue

proc genLvalue(c: var GeneratedCode; t: Tree; n: NodePos; mode: XMode) =
  let info = t[n].info
  case t[n].kind
  of Sym:
    let lit = t[n].litId
    let name = c.m.lits.strings[lit]
    if mode == WantAddr:
      c.code.addParLe VaddrT, info
    c.addSym name, info
    if mode == WantAddr:
      c.code.addParRi()
    c.requestedSyms.incl name
  of DerefC:
    if mode == WantAddr:
      # addr(deref(x)) -> x
      genx(c, t, n.firstSon, WantValue)
    else:
      unOp LoadT
  of AtC:
    if mode == WantValue:
      c.code.addParLe LoadT, info
      genTypeof c, n
    c.buildTree AddscaledT, info:
      genTypeof c, n
      let (a, i) = sons2(t, n)
      genx c, t, a, WantAddr
      genx c, t, i, WantValue
    if mode == WantValue:
      c.code.addParRi()
  of PatC:
    if mode == WantValue:
      c.code.addParLe LoadT, info
      genTypeof c, n
    c.buildTree AddscaledT, info:
      genTypeof c, n
      let (a, i) = sons2(t, n)
      genx c, t, a, WantValue
      genx c, t, i, WantValue
    if mode == WantValue:
      c.code.addParRi()
  of DotC:
    let (obj, fld, _) = sons3(t, n)
    if mode == WantValue:
      c.code.addParLe LoadT, info
      genTypeof c, n
    c.buildTree AddT, info:
      genTypeof c, n
      genx c, t, obj, WantAddr
      genx c, t, fld, WantValue
    if mode == WantValue:
      c.code.addParRi()
  else:
    error c.m, "expected expression but got: ", t, n

proc genStrLit(c: var GeneratedCode; s: string; info: PackedLineInfo) =
  var id = c.strings.getOrDefault(s, -1)
  if id < 0:
    id = c.strings.len + 1
    c.strings[s] = id
    let symId = "str." & $id
    c.data.buildTree AsciizT, info:
      c.data.addSymDef symId, info
      c.data.addStrLit s, info
    addSym c, symId, info
  else:
    let symId = "str." & $id
    addSym c, symId, info

proc genConv(c: var GeneratedCode; t: Tree; n: NodePos) =
  let (typ, arg) = sons2(t, n)
  let src = getAsmSlot(c, arg)
  var dest = AsmSlot()
  fillTypeSlot c, typeFromPos(typ), dest
  let info = t[n].info
  var opc: TagId
  if src.size == dest.size:
    opc = ErrT
  elif src.kind == AFloat and dest.kind != AFloat:
    if dest.kind == AInt:
      opc = FtoiT
    else:
      opc = FtouT
  elif dest.kind == AFloat and src.kind != AFloat:
    if src.kind == AInt:
      opc = ItofT
    else:
      opc = UtofT
  elif src.size > dest.size:
    if dest.kind == AFloat:
      opc = FnarrowT
    else:
      opc = TruncT
  else:
    case dest.kind
    of AUInt, AMem, ABool:
      opc = ZextT
    of AInt:
      opc = SextT
    of AFloat:
      opc = FextT

  if opc != ErrT:
    genSlot c, dest, info
    genSlot c, src, info
  genx c, t, arg, WantValue
  if opc != ErrT:
    c.code.addParRi()

proc declareBoolAndAsgn(c: var GeneratedCode; info: PackedLineInfo): TempVar =
  result = getTempVar(c)
  c.code.buildTree VarT, info:
    c.defineTemp result, info
    c.addEmpty info # no pragmas
    c.addKeyw BT, info
  c.code.addParLe AsgnT, info
  c.addKeyw BT, info
  c.useTemp result, info

proc genCond(c: var GeneratedCode; t: Tree; n: NodePos; opc: TagId) =
  assert opc == FjmpT or opc == TjmpT
  # Preasm has no `and`/`or` operators and we might already be in deeply
  # nested expression based code here. The solution is to "repair" the AST:
  # `(call (add x (add y z)) (and a b)` is rewritten to
  # `(var :tmp (bool)) (asgn tmp a) (fjmp tmp L1) (asgn tmp b)) (lab :L1); (call (add x (add y z)) tmp)`.
  # For this we stored the beginning of the stmt in `c.stmtBegin`.
  var fullExpr = default(TokenBuf)
  for i in c.stmtBegin ..< c.code.len:
    fullExpr.add c.code[i]
  c.code.shrink c.stmtBegin

  let info = t[n].info
  let temp = declareBoolAndAsgn(c, info)
  let (a, b) = sons2(t, n)
  genx c, t, a, WantValue
  c.code.addParRi() # assignment is over
  let lab = getLabel(c)
  c.buildTree opc, info:
    c.useTemp temp, info
    c.useLabel lab, info
  c.buildTree AsgnT, info:
    c.addKeyw BT, info
    c.useTemp temp, info
    genx c, t, b, WantValue
  c.buildTree LabT, info:
    c.defineLabel lab, info
  for i in 0 ..< fullExpr.len:
    c.code.add fullExpr[i]
  c.useTemp temp, info

proc genx(c: var GeneratedCode; t: Tree; n: NodePos; mode: XMode) =
  let info = t[n].info
  case t[n].kind
  of IntLit:
    genIntLit c, t[n].litId, info
  of UIntLit:
    genUIntLit c, t[n].litId, info
  of FloatLit:
    genFloatLit c, t[n].litId, info
  of CharLit:
    let ch = t[n].uoperand
    genCharLit c, char(ch), info
  of FalseC: genCharLit c, char(0), info
  of TrueC: genCharLit c, char(1), info
  of StrLit:
    genStrLit(c, c.m.lits.strings[t[n].litId], info)
  of NilC:
    genIntLit c, 0, info
  of AconstrC:
    if c.inConst > 0:
      for ch in sonsFromX(t, n):
        c.genx t, ch, WantValue
    else:
      error c.m, "runtime array constructor not supported: ", t, n
  of OconstrC:
    if c.inConst > 0:
      for ch in sonsFromX(t, n):
        if t[ch].kind == OconstrC:
          # Inheritance
          c.genx t, ch, WantValue
        else:
          let (_, v) = sons2(t, ch)
          c.genx t, v, WantValue
    else:
      error c.m, "runtime object constructor not supported: ", t, n
  of ParC:
    let arg = n.firstSon
    genx c, t, arg, mode
  of AddrC:
    assert mode == WantValue
    genx c, t, n.firstSon, WantAddr
  of SizeofC:
    # we evaluate it at compile-time:
    let a = getAsmSlot(c, n.firstSon)
    genIntLit c, a.size, info
  of CallC: genCall c, t, n
  of AddC: typedBinOp AddT
  of SubC: typedBinOp SubT
  of MulC: typedBinOp MulT
  of DivC: typedBinOp DivT
  of ModC: typedBinOp ModT
  of ShlC: typedBinOp ShlT
  of ShrC: typedBinOp ShrT
  of BitandC: typedBinOp BitandT
  of BitorC: typedBinOp BitorT
  of BitxorC: typedBinOp BitxorT
  of BitnotC: typedUnOp BitnotT
  of AndC: genCond c, t, n, FjmpT
  of OrC: genCond c, t, n, TjmpT
  of NotC: unOp NotT
  of NegC: unOp NegT
  of EqC: cmpOp EqT
  of LeC: cmpOp LeT
  of LtC: cmpOp LtT
  of CastC, ConvC:
    assert mode == WantValue
    genConv c, t, n
  of SufC:
    let (value, suffix) = sons2(t, n)
    genx(c, t, value, mode)
  else:
    genLvalue c, t, n, mode
