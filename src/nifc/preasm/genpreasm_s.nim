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
  # XXX Needs to `kill` locals here?
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

proc genCaseCond(c: var GeneratedCode; t: Tree; n: NodePos) =
  # BranchValue ::= Number | CharLiteral | Symbol
  # BranchRange ::= BranchValue | (range BranchValue BranchValue)
  # BranchRanges ::= (ranges BranchRange+)
  if t[n].kind == RangesC:
    for ch in sons(t, n):
      c.add CaseKeyword
      if t[ch].kind == RangeC:
        let (a, b) = sons2(t, ch)
        genBranchValue c, t, a
        c.add " ... "
        genBranchValue c, t, b
      else:
        genBranchValue c, t, ch
  else:
    error c.m, "no `ranges` expected but got: ", t, n

proc genSwitch(c: var GeneratedCode; t: Tree; caseStmt: NodePos) =
  # (case Expr (of BranchRanges StmtList)* (else StmtList)?) |
  c.add SwitchKeyword
  c.add ParLe
  let selector = caseStmt.firstSon
  c.genx t, selector
  c.add ParRi
  c.add CurlyLe

  var hasElse = false
  var hasElif = false
  for n in sonsFromX(t, caseStmt):
    case t[n].kind
    of OfC:
      if hasElse:
        error c.m, "no `of` allowed after `else` but got: ", t, n
      else:
        let (cond, action) = sons2(t, n)
        c.genCaseCond t, cond
        c.add CurlyLe
        genStmt c, t, action
        c.add CurlyRi
        c.add BreakKeyword
        c.add Semicolon
      hasElif = true
    of ElseC:
      hasElse = true
      if not hasElif:
        error c.m, "no `of` before `else` but got: ", t, n
      else:
        c.add ElseKeyword
        c.add CurlyLe
        genStmt c, t, n.firstSon
        c.add CurlyRi
        c.add BreakKeyword
        c.add Semicolon
    else:
      error c.m, "`case` expects `of` or `else` but got: ", t, n
  if not hasElif and not hasElse:
    error c.m, "`case` expects `of` or `else` but got: ", t, caseStmt
  c.add CurlyRi

proc genAsgn(c: var GeneratedCode; t: Tree; n: NodePos) =
  let (dest, src) = sons2(t, n)
  let isAsgn = t[dest].kind == Symbol
  let opc = if isAsgn: AsgnT else: StoreT
  c.buildTree opc, t[n].info:
    genTypeof c, dest
    genx c, t, dest, (if isAsgn: WantValue else: WantAddr)
    genx c, t, src, WantValue

proc genReturn(c: var GeneratedCode; t: Tree; n: NodePos) =
  # XXX Needs to `kill` locals here?
  c.buildTree RetT, t[n].info:
    c.genx t, n.firstSon, WantValue

proc genStmt(c: var GeneratedCode; t: Tree; n: NodePos) =
  c.stmtBegin = c.code.len
  case t[n].kind
  of Empty:
    discard
  of StmtsC:
    for ch in sons(t, n):
      genStmt(c, t, ch)
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
