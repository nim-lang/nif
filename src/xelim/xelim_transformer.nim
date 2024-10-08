## Xelim sublanguage
## Eliminate eXpressions in complex situations. In other words turns
## `let x = if cond: 3 else: 4` into
## `let tmp; if cond: tmp = 3 else: temp = 4; let x = tmp`

import std / [assertions, syncio]
import ".." / lib / [packedtrees, lineinfos, bitabs]
import xelim_model, xelim_typenav

proc isComplex(t: Tree; n: NodePos): bool =
  template prop(n: Node; ch: NodePos): bool =
    n.kind in {ExprX}
  hasNodeWithProperty t, n, DeclarativeNodes, prop

type
  Mode = enum
    IsEmpty, IsAppend, IsIgnored
  Target = object
    m: Mode
    t: Tree
  Context = object
    counter: int
    m: Module

proc copy(dest: var Tree; tar: Target) =
  copyTree dest, tar.t, StartPos

proc trExpr(c: var Context; dest: var Tree; t: Tree; n: NodePos; tar: var Target)
proc trStmt(c: var Context; dest: var Tree; t: Tree; n: NodePos)

proc declareTemp(c: var Context; dest: var Tree; t: Tree; n: NodePos): StrId =
  let info = t[n].info
  let typ = getType(c.m, t, n)
  let s = "tmp." & $c.counter & ".01"
  inc c.counter
  result = c.m.lits.strings.getOrIncl(s)
  copyInto dest, VarX, info:
    dest.addAtom SymDef, result, info
    dest.addEmpty 2 # export, pragmas
    copyType dest, t, typ # type
    dest.addEmpty # value

proc declareTempBool(c: var Context; dest: var Tree; info: PackedLineInfo): StrId =
  let s = "tmp." & $c.counter & ".01"
  inc c.counter
  result = c.m.lits.strings.getOrIncl(s)
  copyInto dest, VarX, info:
    dest.addAtom SymDef, result, info
    dest.addEmpty 2 # export, pragmas
    copyInto dest, BoolX, info # type
    dest.addEmpty # value

proc trExprInto(c: var Context; dest: var Tree; t: Tree; n: NodePos; v: StrId) =
  var tar = Target(m: IsEmpty)
  trExpr c, dest, t, n, tar

  let info = t[n].info
  copyInto dest, AsgnX, info:
    dest.addAtom Sym, v, info
    dest.copy tar

proc trOr(c: var Context; dest: var Tree; t: Tree; n: NodePos; tar: var Target) =
  if isComplex(t, n):
    let (a, b) = sons2(t, n)
    # `x or y`  <=> `if x: true else: y` <=> `if x: tmp = true else: tmp = y`
    let info = t[n].info
    var tmp = declareTempBool(c, dest, info)

    var aa = Target(m: IsEmpty)
    trExpr c, dest, t, a, aa
    copyInto dest, IfX, info:
      copyInto dest, ElifX, info:
        dest.copy aa                # if x
        copyInto dest, StmtsX, info:
          copyInto dest, AsgnX, info: # tmp = true
            dest.addAtom Sym, tmp, info
            dest.copyInto TrueX, info
      copyInto dest, ElseX, info:
        copyInto dest, StmtsX, info:
          trExprInto c, dest, t, b, tmp # tmp = y
    tar.t.addAtom Sym, tmp, info
  else:
    for ch in wsons(tar.t, t, n):
      trExpr c, dest, t, ch, tar

proc trAnd(c: var Context; dest: var Tree; t: Tree; n: NodePos; tar: var Target) =
  if isComplex(t, n):
    let (a, b) = sons2(t, n)
    # `x and y` <=> `if x: y else: false` <=> `if x: tmp = y else: tmp = false`
    let info = t[n].info
    var tmp = declareTempBool(c, dest, info)

    var aa = Target(m: IsEmpty)
    trExpr c, dest, t, a, aa
    copyInto dest, IfX, info:
      copyInto dest, ElifX, info:
        dest.copy aa                # if x
        copyInto dest, StmtsX, info:
          trExprInto c, dest, t, b, tmp # tmp = y
      copyInto dest, ElseX, info:
        copyInto dest, StmtsX, info:
          # tmp = false
          copyInto dest, AsgnX, info:
            dest.addAtom Sym, tmp, info
            dest.copyInto FalseX, info
    tar.t.addAtom Sym, tmp, info
  else:
    for ch in wsons(tar.t, t, n):
      trExpr c, dest, t, ch, tar

proc trIf(c: var Context; dest: var Tree; t: Tree; n: NodePos; tar: var Target) =
  # if cond: a elif condB: b else: c
  # -->
  # if cond: a else: (if condB: b else: c)
  let info = t[n].info
  var tmp = StrId(0)

  if tar.m != IsIgnored:
    tmp = declareTemp(c, dest, t, n)

  var positions: seq[PatchPos] = @[]
  for ch in sons(t, n):
    let info = t[ch].info
    case t[ch].kind
    of ElifX:
      let (cond, action) = sons2(t, ch)
      var t0 = Target(m: IsEmpty)
      trExpr c, dest, t, cond, t0

      positions.add prepare(dest, IfX, info)

      copyInto dest, ElifX, info:
        dest.copy t0
        copyInto dest, StmtsX, info:
          if tar.m != IsIgnored:
            trExprInto c, dest, t, action, tmp
          else:
            trStmt c, dest, t, action

      if not isLastSon(t, n, ch):
        positions.add prepare(dest, ElseX, info)
        positions.add prepare(dest, StmtsX, info)

    of ElseX:
      let action = ch.firstSon
      if tar.m != IsIgnored:
        trExprInto c, dest, t, action, tmp
      else:
        trStmt c, dest, t, action
    else:
      # Bug: just copy the thing around
      copyTree dest, t, n

  for p in items(positions):
    patch dest, p

  if tar.m != IsIgnored:
    tar.t.addAtom Sym, tmp, info

proc trCase(c: var Context; dest: var Tree; t: Tree; n: NodePos; tar: var Target) =
  let info = t[n].info
  var tmp = StrId(0)

  if tar.m != IsIgnored:
    tmp = declareTemp(c, dest, t, n)

  var t0 = Target(m: IsEmpty)
  trExpr c, dest, t, n.firstSon, t0
  copyIntoFrom(dest, t, n):
    dest.copy t0
    for ch in sonsFromX(t, n):
      case t[ch].kind
      of OfX:
        copyIntoFrom(dest, t, ch):
          let (choices, action) = sons2(t, ch)
          copyTree dest, t, choices
          copyInto dest, StmtsX, info:
            if tar.m != IsIgnored:
              trExprInto c, dest, t, action, tmp
            else:
              trStmt c, dest, t, action
      of ElseX:
        copyIntoFrom(dest, t, ch):
          let action = ch.firstSon
          copyInto dest, StmtsX, info:
            if tar.m != IsIgnored:
              trExprInto c, dest, t, action, tmp
            else:
              trStmt c, dest, t, action
      else:
        # Bug: just copy the thing around
        copyTree dest, t, n
  if tar.m != IsIgnored:
    tar.t.addAtom Sym, tmp, info

proc trTry(c: var Context; dest: var Tree; t: Tree; n: NodePos; tar: var Target) =
  let info = t[n].info
  var tmp = StrId(0)

  if tar.m != IsIgnored:
    tmp = declareTemp(c, dest, t, n)

  copyIntoFrom(dest, t, n):
    if tar.m != IsIgnored:
      trExprInto c, dest, t, n.firstSon, tmp
    else:
      trStmt c, dest, t, n.firstSon

    for ch in sonsFromX(t, n):
      case t[ch].kind
      of ExceptX:
        copyIntoFrom(dest, t, ch):
          for e in sons(t, ch):
            if isLastSon(t, ch, e):
              if tar.m != IsIgnored:
                trExprInto c, dest, t, e, tmp
              else:
                trStmt c, dest, t, e
            else:
              copyTree dest, t, e
      of FinallyX:
        # The `finally` section never produces a value!
        copyIntoFrom(dest, t, ch):
          let action = ch.firstSon
          trStmt c, dest, t, action
      else:
        # Bug: just copy the thing around
        copyTree dest, t, n
  if tar.m != IsIgnored:
    tar.t.addAtom Sym, tmp, info

proc trStmt(c: var Context; dest: var Tree; t: Tree; n: NodePos) =
  case t[n].kind
  of Empty, Tag:
    copyTree dest, t, n
  of Ident, Sym, Symdef, IntLit, UIntLit, FloatLit, CharLit, StrLit:
    # cannot really happen here
    assert false
  of IfX:
    var tar = Target(m: IsIgnored)
    trIf c, dest, t, n, tar
  of CaseX:
    var tar = Target(m: IsIgnored)
    trCase c, dest, t, n, tar
  of TryX:
    var tar = Target(m: IsIgnored)
    trTry c, dest, t, n, tar

  of RetX, DiscardX, RaiseX, YieldX:
    var tar = Target(m: IsEmpty)
    trExpr c, dest, t, n.firstSon, tar
    dest.copyIntoFrom t, n:
      dest.copy tar

  of WhileX:
    let (cond, body) = sons2(t, n)
    let info = t[n].info
    dest.copyIntoFrom t, n:
      if isComplex(t, cond):
        dest.copyInto TrueX, info
        copyInto dest, StmtsX, info:
          var tar = Target(m: IsEmpty)
          trExpr c, dest, t, cond, tar
          dest.copyInto IfX, info:
            dest.copyInto ElifX, info:
              dest.copy tar
              trStmt c, dest, t, body
            dest.copyInto ElseX, info:
              dest.copyInto BreakX, info
      else:
        var tar = Target(m: IsEmpty)
        trExpr c, dest, t, cond, tar
        dest.copy tar
        trStmt c, dest, t, body
  of AsgnX, CallX:
    # IMPORTANT: Stores into `tar` helper!
    var tar = Target(m: IsAppend)
    tar.t.copyIntoFrom t, n:
      for ch in sons(t, n):
        trExpr c, dest, t, ch, tar
    dest.copy tar
  of LetX, VarX, CursorX, ConstX:
    var tar = Target(m: IsAppend)
    for ch in wsons(tar.t, t, n):
      if isLastSon(t, n, ch):
        var v = Target(m: IsEmpty)
        trExpr c, dest, t, ch, v
        tar.t.copy v
      else:
        tar.t.copyTree t, ch
    dest.copy tar

  of ProcX:
    for ch in wsons(dest, t, n):
      if isLastSon(t, n, ch):
        trStmt c, dest, t, ch
      else:
        dest.copyTree t, ch
  else:
    for ch in wsons(dest, t, n):
      trStmt c, dest, t, ch

proc trExpr(c: var Context; dest: var Tree; t: Tree; n: NodePos; tar: var Target) =
  # can have the dangerous `Expr` node which is the whole
  # reason for xelim's existance.
  case t[n].kind
  of Empty, Ident, Sym, Symdef, IntLit, UIntLit, FloatLit, CharLit, StrLit, Tag:
    copyTree tar.t, t, n
  of ExprX:
    let (s, x) = sons2(t, n)
    trStmt c, dest, t, s
    trExpr c, dest, t, x, tar
  of IfX:
    trIf c, dest, t, n, tar
  of CaseX:
    trCase c, dest, t, n, tar
  of TryX:
    trTry c, dest, t, n, tar
  of AndX:
    trAnd c, dest, t, n, tar
  of OrX:
    trOr c, dest, t, n, tar
  else:
    for ch in wsons(tar.t, t, n):
      trExpr c, dest, t, ch, tar

proc transformCode*(inp, outp: string) =
  var m = load(inp)
  # assume 1% code size increase:
  var dest = createPackedTree[XelimKind](m.code.len * 11 div 10)
  var c = Context(m: ensureMove(m))
  trStmt c, dest, c.m.code, StartPos
  writeFile outp, toString(dest, StartPos, c.m.lits)
