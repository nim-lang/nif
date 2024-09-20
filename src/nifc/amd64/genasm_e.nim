#
#
#           NIFC Compiler
#        (c) Copyright 2024 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# included from genpreasm.nim

proc emitLoc*(c: var GeneratedCode; loc: Location) =
  case loc.kind
  of Undef:
    assert false, "location should have been set"
  of ImmediateInt:
    c.code.add toToken(IntLit, pool.integers.getOrIncl(loc.ival), NoLineInfo)
  of ImmediateUInt:
    c.code.add toToken(UIntLit, pool.uintegers.getOrIncl(loc.uval), NoLineInfo)
  of ImmediateFloat:
    c.code.add toToken(FloatLit, pool.floats.getOrIncl(loc.fval), NoLineInfo)
  of InReg, InPushedReg:
    c.addKeywUnchecked regName(loc.reg)
  of InRegFp:
    c.addKeywUnchecked regName(loc.regf)
  of InStack:
    c.buildTree Mem2T:
      c.addKeyw RspT
      c.code.add toToken(IntLit, pool.integers.getOrIncl(loc.slot), NoLineInfo)
  of InFlag:
    assert false, "not implemented"
  of JumpMode:
    c.code.add toToken(Ident, pool.strings.getOrIncl("L." & $loc.label), NoLineInfo)
  of InData:
    c.buildTree RelT:
      c.code.add toToken(Symbol, pool.syms.getOrIncl(c.m.lits.strings[loc.data]), NoLineInfo)
  of InTls:
    c.buildTree FsT:
      c.code.add toToken(Symbol, pool.syms.getOrIncl(c.m.lits.strings[loc.data]), NoLineInfo)

proc genx(c: var GeneratedCode; t: Tree; n: NodePos; dest: var Location)

proc gen(c: var GeneratedCode; t: Tree; n: NodePos): Location =
  result = Location(kind: Undef)
  genx c, t, n, result

proc makeReg(c: var GeneratedCode; x: Location): Location =
  if x.kind != InReg:
    result = scratchReg(c.rega)
    if result.kind == Undef:
      c.buildTree PushT:
        c.addKeyw RcxT   # Rcx is as good as any other
      result = Location(kind: InPushedReg, reg: Rcx)
    c.buildTree MovT:
      c.addKeyw RcxT
      emitLoc c, x
  else:
    result = x

proc genForceReg(c: var GeneratedCode; t: Tree; n: NodePos): Location =
  result = Location(kind: Undef)
  genx c, t, n, result
  result = makeReg(c, result)

proc freeTemp(c: var GeneratedCode; loc: Location) =
  if loc.kind == InPushedReg:
    assert(not loc.temp, "pushed reg must not be marked as temporary")
    c.buildTree PopT:
      emitLoc c, loc
    # KEEP THE REGISTER MARKED AS "USED"! Do not call `freeTempRaw` here!
  else:
    freeTempRaw c.rega, loc

proc combine(c: var GeneratedCode; a, b: Location; opc: TagId) =
  # x86 has no Mem-Mem operations for ALU operations, so instead of
  # Mem[a] + Mem[b] we need to produce `mov reg, Mem[b]; Mem[a] + reg`
  # We need a scratch register to accomplish that. If we have no available
  # we push&pop a used register.
  if invalidCombination(a, b):
    let tmp = makeReg(c, b)
    c.buildTree opc:
      emitLoc c, a
      emitLoc c, tmp
    c.freeTemp tmp
  else:
    c.buildTree opc:
      emitLoc c, a
      emitLoc c, b

template typedBinOp(opr) {.dirty.} =
  let (typ, a, b) = sons3(t, n)
  let x = gen(c, t, a)
  let y = gen(c, t, b)
  c.combine x, y, opr
  freeTemp c, y
  freeTemp c, x

template cmpOp(opr) {.dirty.} =
  c.buildTree opr:
    let (a, b) = sons2(t, n)
    genTypeof c, a
    genx c, t, a, WantValue
    genx c, t, b, WantValue

template unOp(opr) {.dirty.} =
  c.buildTree opr:
    genTypeof c, n.firstSon
    genx c, t, n.firstSon, WantValue

template typedUnOp(opr) {.dirty.} =
  let (typ, a) = sons2(t, n)
  c.buildTree opr:
    genType c, typ
    genx c, t, a, WantValue

proc genAsgn(c: var GeneratedCode; dest, src: Location) =
  if dest.fp:
    c.buildTree MovapdT:
      c.emitLoc dest
      c.emitLoc src
  elif dest.size < 0'i32 or dest.size > 8'i32:
    assert dest.size > 0'i32, "size not set!"
    assert false, "implement rep byte copy loop"
  else:
    c.buildTree MovT:
      c.emitLoc dest
      c.emitLoc src

proc into(c: var GeneratedCode; dest: var Location; src: Location) =
  if dest.kind == Undef:
    dest = src
  else:
    genAsgn c, dest, src

proc genCall(c: var GeneratedCode; t: Tree; n: NodePos; dest: var Location) =
  var args: seq[NodePos] = @[] # so that we can also do it backwards
  for ch in sons(t, n): args.add ch

  let sig = asProcType(t, getType(c.m, t, n.firstSon).rawPos)
  var stackSpace = StackRedZone
  var argTypes: seq[AsmSlot] = @[]
  for param in sons(t, sig.params):
    let p = asParamDecl(t, param)
    argTypes.add c.typeToSlot(p.typ)

  # we use this "RegAllocator" here only to compute the where the
  # expressions need to end up:
  var regb = initRegAllocator()
  if t[sig.returnType].kind in {VoidC, Empty}:
    discard "no return type"
  else:
    let ts = c.typeToSlot(sig.returnType)
    var dummy = default(Location)
    allocResultWin64(regb, ts, dummy)
  var argLocs: seq[Location] = @[]
  for argType in argTypes:
    argLocs.add regb.allocParamWin64(argType)
  reverseStackParamsWin64 argLocs

  for i in 1 ..< args.len:
    genx c, t, args[i], argLocs[i-1]

  let fn = gen(c, t, n.firstSon)
  c.buildTreeI CallT, t[n].info:
    c.emitLoc fn

  if t[sig.returnType].kind in {VoidC, Empty}:
    discard "no return type"
  else:
    let ts = c.typeToSlot(sig.returnType)
    stackSpace += stackSpaceResultWin64(ts)
    if dest.kind == Undef:
      dest = resultWin64(ts)
    else:
      c.genAsgn(dest, resultWin64(ts))

proc genLvalue(c: var GeneratedCode; t: Tree; n: NodePos; dest: var Location) =
  let info = t[n].info
  case t[n].kind
  of Sym:
    let lit = t[n].litId
    let def = c.m.defs.getOrDefault(lit)
    case def.kind
    of ConstC:
      let cnst = asVarDecl(t, def.pos)
      genLvalue(c, t, cnst.value, dest)
    of ProcC:
      let d = Location(size: 8, kind: InData, data: lit)
      into c, dest, d
    of VarC, ParamC:
      into c, dest, c.locals[lit]
    of GvarC:
      let d = Location(indirect: true, size: 8, kind: InData, data: lit)
      into c, dest, d
    of TvarC:
      let d = Location(indirect: true, size: 8, kind: InTls, data: lit)
      into c, dest, d
    of EfldC:
      assert false, "enum fields not implemented"
    else:
      error c.m, "undeclared identifier: ", t, n
    #let lit = t[n].litId
    #let name = c.m.lits.strings[lit]
    #c.addSym name, info
  of DerefC:
    let tmp = genForceReg(c, t, n.firstSon)
    c.buildTreeI Mem1T, t[n].info:
      c.emitLoc tmp
    c.freeTemp tmp
  of AtC:
    let elemType = getType(m, t, n)
    let (a, i) = sons2(t, n)
    let tmp = gen(c, t, a)

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

proc genStrLit(c: var GeneratedCode; s: string; info: PackedLineInfo; dest: var Location) =
  var id = c.strings.getOrDefault(s, -1)
  var symId: string
  if id < 0:
    id = c.strings.len + 1
    c.strings[s] = id
    symId = "str." & $id
    c.rodata.buildTree DbT, info:
      c.rodata.addSymDef symId, info
      c.rodata.addStrLit s, info
      c.rodata.addIntLit 0, info
  else:
    symId = "str." & $id
  let d = Location(size: -1'i32, kind: InData, data: pool.syms.getOrIncl(symId))
  into c, dest, d

proc genConv(c: var GeneratedCode; t: Tree; n: NodePos; dest: var Location) =
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

proc genFjmp(c: var GeneratedCode; t: Tree; n: NodePos; jmpTarget: Label; opc = FjmpT) =
  let info = t[n].info
  let k = t[n].kind
  case k
  of ParC:
    genFjmp c, t, n.firstSon, jmpTarget, opc
  of NotC:
    genFjmp c, t, n.firstSon, jmpTarget, (if opc == FjmpT: TjmpT else: FjmpT)
  of AndC, OrC:
    if (k == AndC and opc == FjmpT) or
       (k == OrC and opc == TjmpT):
      # easy case
      let (a, b) = sons2(t, n)
      genFjmp c, t, a, jmpTarget, opc
      genFjmp c, t, b, jmpTarget, opc
    else:
      # "or" case:
      let (a, b) = sons2(t, n)
      # "if not a: b"
      let neg = (if opc == FjmpT: TjmpT else: FjmpT)
      let lab = getLabel(c)
      genFjmp c, t, a, lab, neg
      genFjmp c, t, b, jmpTarget, opc
      c.buildTree LabT, info:
        c.defineLabel lab, info
  else:
    c.buildTree opc, info:
      genx c, t, n, WantValue
      c.useLabel jmpTarget, info

proc genx(c: var GeneratedCode; t: Tree; n: NodePos; dest: var Location) =
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
      error c.m, "runtime array constructor not implemented: ", t, n
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
      error c.m, "runtime object constructor not implemented: ", t, n
  of ParC:
    let arg = n.firstSon
    genx c, t, arg, dest
  of AddrC:
    genx c, t, n.firstSon, dest
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
    genLvalue c, t, n, mode, dest
