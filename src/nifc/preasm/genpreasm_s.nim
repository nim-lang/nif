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
    c.buildTree JmpT, t[n].info:
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
  c.buildTree LoopT, t[n].info:
    c.defineLabel loopLabel, t[n].info
  c.buildTree FjmpT, t[cond].info:
    c.genx t, cond, WantValue
    c.useLabel exit, t[cond].info
  c.genStmt t, body
  c.buildTree JloopT, t[n].info:
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
        c.buildTree FjmpT, t[n].info:
          c.genx t, cond, WantValue
          c.useLabel afterwards, t[n].info
        genStmt c, t, action
        c.buildTree JmpT, t[n].info:
          c.useLabel endif, t[n].info
        c.buildTree LabT, t[n].info:
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
  c.buildTree LabT, t[ifStmt].info:
    c.defineLabel endif, t[ifStmt].info

proc genLabel(c: var GeneratedCode; t: Tree; n: NodePos) =
  let dname = n.firstSon
  if t[dname].kind == SymDef:
    let lit = t[dname].litId
    let name = c.m.lits.strings[lit]
    c.buildTree LabT, t[n].info:
      c.code.addSymDef name, t[dname].info
  else:
    error c.m, "expected SymbolDef but got: ", t, n

proc genGoto(c: var GeneratedCode; t: Tree; n: NodePos) =
  let dname = n.firstSon
  if t[dname].kind == Sym:
    let lit = t[dname].litId
    let name = c.m.lits.strings[lit]
    c.buildTree JmpT, t[n].info:
      c.addSym name, t[dname].info
  else:
    error c.m, "expected Symbol but got: ", t, n

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
          c.buildTree LabT, info:
            c.defineLabel Label(afterwards), info
        let action = getLabel(c)
        let (cond, stmts) = sons2(t, n)
        c.genCaseCond t, cond, sel, seltyp, action

        afterwards = getLabel(c).int
        c.buildTree JmpT, info:
          c.useLabel Label(afterwards), info

        c.buildTree LabT, info:
          c.defineLabel action, info
        genStmt c, t, stmts

        c.buildTree JmpT, info:
          c.useLabel endif, info
        c.buildTree LabT, info:
          c.defineLabel Label(afterwards), info

      hasElif = true
    of ElseC:
      hasElse = true
      if not hasElif:
        error c.m, "no `of` before `else` but got: ", t, n
      else:
        if afterwards >= 0:
          c.buildTree LabT, info:
            c.defineLabel Label(afterwards), info
        genStmt c, t, n.firstSon
    else:
      error c.m, "`case` expects `of` or `else` but got: ", t, n
  if not hasElif and not hasElse:
    error c.m, "`case` expects `of` or `else` but got: ", t, caseStmt
  c.buildTree LabT, t[caseStmt].info:
    c.defineLabel endif, t[caseStmt].info

proc genAsgn(c: var GeneratedCode; t: Tree; n: NodePos) =
  let (dest, src) = sons2(t, n)
  let isAsgn = t[dest].kind == Sym
  let opc = if isAsgn: AsgnT else: StoreT
  c.buildTree opc, t[n].info:
    genTypeof c, dest
    genx c, t, dest, (if isAsgn: WantValue else: WantAddr)
    genx c, t, src, WantValue

proc genReturn(c: var GeneratedCode; t: Tree; n: NodePos) =
  c.buildTree RetT, t[n].info:
    genTypeof c, n.firstSon
    c.genx t, n.firstSon, WantValue

proc genStmt(c: var GeneratedCode; t: Tree; n: NodePos) =
  c.stmtBegin = c.code.len
  case t[n].kind
  of Empty:
    discard
  of StmtsC, ScopeC:
    c.openScope()
    c.buildTree StmtsT, t[n].info:
      for ch in sons(t, n):
        genStmt(c, t, ch)
    c.closeScope()
  of CallC:
    genCall c, t, n
  of VarC:
    genVarDecl c, t, n, IsLocal
  of GvarC:
    moveToDataSection:
      genVarDecl c, t, n, IsGlobal
  of TvarC:
    moveToDataSection:
      genVarDecl c, t, n, IsThreadlocal
  of ConstC:
    moveToDataSection:
      genConstDecl c, t, n
  of EmitC:
    genEmitStmt c, t, n
  of AsgnC: genAsgn c, t, n
  of IfC: genIf c, t, n
  of WhileC: genWhile c, t, n
  of BreakC: genBreak c, t, n
  of CaseC: genSwitch c, t, n
  of LabC: genLabel c, t, n
  of JmpC: genGoto c, t, n
  of RetC: genReturn c, t, n
  else:
    error c.m, "expected statement but got: ", t, n
