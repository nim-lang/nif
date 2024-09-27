#
#
#           NIFC Compiler
#        (c) Copyright 2024 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# included from genpreasm.nim

proc genEmitStmt(c: var GeneratedCode; t: Tree; n: NodePos) =
  error c.m, "'emit' statement is not supported", t, n

proc genStmt(c: var GeneratedCode; t: Tree; n: NodePos)

proc genBreak(c: var GeneratedCode; t: Tree; n: NodePos) =
  # XXX Needs to `kill` locals here?
  if c.loopExits.len == 0:
    error c.m, "`break` not within a loop: ", t, n
  else:
    c.buildTreeI JmpT, t[n].info:
      c.useLabel c.loopExits[^1], t[n].info

proc genWhile(c: var GeneratedCode; t: Tree; n: NodePos) =
  #[
     LoopLabel:
       fjmp cond, LoopExit
       stmts
       jloop LoopLabel
     LoopExit:

  ]#
  let exit = getLabel(c)
  let loopLabel = getLabel(c)
  c.loopExits.add exit
  let (cond, body) = sons2(t, n)
  c.defineLabel loopLabel, t[n].info, LooplabT
  var d = Location(kind: JumpMode, label: int(exit))
  c.genx t, cond, d
  c.useLabel exit, t[cond].info
  c.genStmt t, body
  c.buildTreeI JloopT, t[n].info:
    c.useLabel loopLabel, t[n].info
  discard c.loopExits.pop()

proc genIf(c: var GeneratedCode; t: Tree; ifStmt: NodePos) =
  var hasElse = false
  var hasElif = false
  let endif = getLabel(c)
  for n in sons(t, ifStmt):
    case t[n].kind
    of ElifC:
      if hasElse:
        error c.m, "no `elif` allowed after `else` but got: ", t, n
      else:
        let (cond, action) = sons2(t, n)
        let afterwards = getLabel(c)
        var d = Location(kind: JumpMode, label: int(afterwards))
        c.genx t, cond, d
        genStmt c, t, action
        c.buildTreeI JmpT, t[n].info:
          c.useLabel endif, t[n].info
        c.defineLabel afterwards, t[n].info
      hasElif = true
    of ElseC:
      hasElse = true
      if not hasElif:
        error c.m, "no `elif` before `else` but got: ", t, n
      else:
        genStmt c, t, n.firstSon
    else:
      error c.m, "`if` expects `elif` or `else` but got: ", t, n
  if not hasElif and not hasElse:
    error c.m, "`if` expects `elif` or `else` but got: ", t, ifStmt
  c.defineLabel endif, t[ifStmt].info

proc genLabel(c: var GeneratedCode; t: Tree; n: NodePos) =
  let dname = n.firstSon
  if t[dname].kind == SymDef:
    let lit = t[dname].litId
    let name = c.m.lits.strings[lit]
    c.buildTreeI LabT, t[n].info:
      c.code.addSymDef name, t[dname].info
  else:
    error c.m, "expected SymbolDef but got: ", t, n

proc genGoto(c: var GeneratedCode; t: Tree; n: NodePos) =
  let dname = n.firstSon
  if t[dname].kind == Sym:
    let lit = t[dname].litId
    let name = c.m.lits.strings[lit]
    c.buildTreeI JmpT, t[n].info:
      c.addSym name, t[dname].info
  else:
    error c.m, "expected Symbol but got: ", t, n

# XXX `case` not implemented

#[
proc genBranchValue(c: var GeneratedCode; t: Tree; n: NodePos) =
  if t[n].kind in {NifcKind.IntLit, UIntLit, CharLit, Sym}:
    c.genx t, n, WantValue
  else:
    error c.m, "expected valid `of` value but got: ", t, n

proc genCaseCond(c: var GeneratedCode; t: Tree; n: NodePos;
                 tmp: TempVar; tmptyp: AsmSlot; action: Label) =
  # BranchValue ::= Number | CharLiteral | Symbol
  # BranchRange ::= BranchValue | (range BranchValue BranchValue)
  # BranchRanges ::= (ranges BranchRange+)
  if t[n].kind == RangesC:
    for ch in sons(t, n):
      let info = t[ch].info
      if t[ch].kind == RangeC:
        let (a, b) = sons2(t, ch)
        c.buildTree TjmpT, info:
          c.buildTree BitandT, info:
            c.addKeyw BT, info
            c.buildTree LeT, info:
              genSlot c, tmptyp, info # type
              genBranchValue c, t, a
              c.useTemp tmp, info

            c.buildTree LeT, info:
              genSlot c, tmptyp, info # type
              c.useTemp tmp, info
              genBranchValue c, t, b
          c.useLabel action, info
      else:
        c.buildTree TjmpT, info:
          c.buildTree EqT, info:
            genSlot c, tmptyp, info # type
            c.useTemp tmp, info
            genBranchValue c, t, ch
          c.useLabel action, info
  else:
    error c.m, "no `ranges` expected but got: ", t, n

proc genSwitch(c: var GeneratedCode; t: Tree; caseStmt: NodePos) =
  # (case Expr (of BranchRanges StmtList)* (else StmtList)?) |
  let sel = getTempVar(c)
  let selector = caseStmt.firstSon
  let seltyp = getAsmSlot(c, selector)
  let info = t[selector].info
  c.code.buildTree VarT, info:
    c.defineTemp sel, info
    c.addEmpty info # no pragmas
    genSlot c, seltyp, info

  c.buildTree AsgnT, info:
    genSlot c, seltyp, info
    c.useTemp sel, info
    c.genx t, selector, WantValue

  var hasElse = false
  var hasElif = false
  var afterwards = -1
  let endif = getLabel(c)
  for n in sonsFromX(t, caseStmt):
    let info = t[n].info
    case t[n].kind
    of OfC:
      if hasElse:
        error c.m, "no `of` allowed after `else` but got: ", t, n
      else:
        if afterwards >= 0:
          c.defineLabel Label(afterwards), info
        let action = getLabel(c)
        let (cond, stmts) = sons2(t, n)
        c.genCaseCond t, cond, sel, seltyp, action

        afterwards = getLabel(c).int
        c.buildTree JmpT, info:
          c.useLabel Label(afterwards), info

        c.defineLabel action, info
        genStmt c, t, stmts

        c.buildTree JmpT, info:
          c.useLabel endif, info
        c.defineLabel Label(afterwards), info

      hasElif = true
    of ElseC:
      hasElse = true
      if not hasElif:
        error c.m, "no `of` before `else` but got: ", t, n
      else:
        if afterwards >= 0:
          c.defineLabel Label(afterwards), info
        genStmt c, t, n.firstSon
    else:
      error c.m, "`case` expects `of` or `else` but got: ", t, n
  if not hasElif and not hasElse:
    error c.m, "`case` expects `of` or `else` but got: ", t, caseStmt
  c.defineLabel endif, t[caseStmt].info
]#

proc genProlog*(c: var GeneratedCode) =
  discard

proc genEpilog*(c: var GeneratedCode) =
  discard

proc getExitProcLabel(c: var GeneratedCode): Label =
  if c.exitProcLabel.int < 0:
    c.exitProcLabel = getLabel(c)
  result = c.exitProcLabel

proc genReturn(c: var GeneratedCode; t: Tree; n: NodePos) =
  var d = resultWin64(getAsmSlot(c, n))
  c.genx t, n.firstSon, d
  let lab = getExitProcLabel(c)
  # we don't generate a `ret` instruction as we might need to
  # free the stack and we don't know yet how much stack we need!
  c.buildTreeI JmpT, t[n].info:
    c.useLabel lab, t[n].info

proc genLocalVar(c: var GeneratedCode; t: Tree; n: NodePos) =
  let v = asVarDecl(t, n)
  assert t[v.name].kind == SymDef
  let name = t[v.name].litId
  assert c.locals.hasKey(name)
  if t[v.value].kind != Empty:
    # generate the assignment:
    genx c, t, v.value, c.locals[name]

proc genConstData(c: var GeneratedCode; t: Tree; n: NodePos) =
  let info = t[n].info
  case t[n].kind
  of Sym:
    # reference to a proc or to some other address that will be resolved
    # during linking:
    c.addSym c.m.lits.strings[t[n].litId], info
  of CharLit:
    let ch = t[n].uoperand
    c.genIntLit int(ch), info
  of FloatLit:
    c.genFloatLit t[n].litId, info
  of IntLit:
    c.genIntLit t[n].litId, info
  of UIntLit:
    c.genUIntLit t[n].litId, info
  of FalseC:
    c.genIntLit 0, info
  of TrueC:
    c.genIntLit 1, info
  of StrLit:
    var dest = Location(kind: Undef)
    genStrLit(c, c.m.lits.strings[t[n].litId], info, dest)
    c.addSym c.m.lits.strings[dest.data], info
  of NilC:
    c.genIntLit 0, info
  of AconstrC:
    for ch in sonsFromX(t, n):
      c.genConstData t, ch
  of OconstrC:
    for ch in sonsFromX(t, n):
      if t[ch].kind == OconstrC:
        # Inheritance
        c.genConstData t, ch
      else:
        let (_, v) = sons2(t, ch)
        c.genConstData t, v
  of ParC:
    let arg = n.firstSon
    genConstData c, t, arg
  of SizeofC:
    let a = getAsmSlot(c, n.firstSon)
    c.genIntLit a.size, info
  else:
    error c.m, "unsupported expression for const: ", t, n

proc genGlobalVar(c: var GeneratedCode; t: Tree; n: NodePos) =
  let where = if t[n].kind == TvarC: InTls else: InData
  let v = asVarDecl(t, n)
  assert t[v.name].kind == SymDef
  let name = t[v.name].litId
  var d = Location(flags: {Indirect}, typ: typeToSlot(c, v.typ), kind: where)
  d.data = name
  c.globals[name] = d

  let opc =
    case d.typ.align
    of 1: DbT
    of 2: DwT
    of 4: DdT
    of 8: DqT
    else: DqT # bigger alignments are not really supported for now

  if t[n].kind == ConstC:
    c.buildTreeI RodataT, t[n].info:
      c.buildTree opc:
        c.code.addSymDef c.m.lits.strings[name], t[v.name].info
        c.genConstData t, v.value

  else:
    c.buildTreeI DataT, t[n].info:
      c.buildTree opc:
        c.code.addSymDef c.m.lits.strings[name], t[v.name].info
        c.buildTree TimesT:
          c.genIntLit d.typ.size div min(d.typ.align, 8), t[n].info
          c.genIntLit 0, t[n].info

    if t[v.value].kind != Empty:
      # generate the assignment:
      genx c, t, v.value, d

proc genStmt(c: var GeneratedCode; t: Tree; n: NodePos) =
  case t[n].kind
  of Empty:
    discard
  of StmtsC, ScopeC:
    for ch in sons(t, n):
      genStmt(c, t, ch)
  of CallC:
    var d = Location(kind: Undef)
    genCall c, t, n, d
  of VarC:
    genLocalVar c, t, n
  of GvarC, TvarC, ConstC:
    moveToDataSection:
      genGlobalVar c, t, n
  #of EmitC:
  #  genEmitStmt c, t, n
  of AsgnC: genAsgn c, t, n
  of IfC: genIf c, t, n
  of WhileC: genWhile c, t, n
  of BreakC: genBreak c, t, n
  #of CaseC: genSwitch c, t, n
  of LabC: genLabel c, t, n
  of JmpC: genGoto c, t, n
  of RetC: genReturn c, t, n
  else:
    error c.m, "expected statement but got: ", t, n
