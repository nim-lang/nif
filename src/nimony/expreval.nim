## expression evaluator for simple constant expressions, not meant to be complete

include nifprelude
import nimony_model, decls, programs, xints

type
  EvalContext* = object
    values: seq[TokenBuf]
    trueValue, falseValue: Cursor

proc isConstBoolValue*(n: Cursor): bool =
  n.exprKind in {TrueX, FalseX}

proc isConstIntValue*(n: Cursor): bool =
  n.kind == IntLit

proc isConstUIntValue*(n: Cursor): bool =
  n.kind == UIntLit

proc isConstStringValue*(n: Cursor): bool =
  n.kind == StringLit

proc isConstCharValue*(n: Cursor): bool =
  n.kind == CharLit

proc initEvalContext*(): EvalContext =
  result = EvalContext(values: @[])

proc skipParRi(n: var Cursor) =
  if n.kind == ParRi:
    inc n
  else:
    error "expected ')', but got: ", n

proc error(c: var EvalContext, msg: string, info: PackedLineInfo): Cursor =
  let i = c.values.len
  c.values.add createTokenBuf(3)
  c.values[i].addParLe ErrT, info
  c.values[i].addStrLit msg
  c.values[i].addParRi()
  result = cursorAt(c.values[i], 0)

proc getTrueValue(c: var EvalContext): Cursor =
  if c.trueValue == default(Cursor):
    let i = c.values.len
    c.values.add createTokenBuf(2)
    c.values[i].addParLe(TrueX, NoLineInfo)
    c.values[i].addParRi()
    c.trueValue = cursorAt(c.values[i], 0)
  result = c.trueValue

proc getFalseValue(c: var EvalContext): Cursor =
  if c.falseValue == default(Cursor):
    let i = c.values.len
    c.values.add createTokenBuf(2)
    c.values[i].addParLe(FalseX, NoLineInfo)
    c.values[i].addParRi()
    c.falseValue = cursorAt(c.values[i], 0)
  result = c.falseValue

proc eval*(c: var EvalContext, n: var Cursor): Cursor =
  template error(msg: string, info: PackedLineInfo) =
    result = c.error(msg, info)
  template propagateError(r: Cursor): Cursor =
    let val = r
    if val.kind == ParLe and val.tagId == ErrT:
      val
    else:
      return val
  case n.kind
  of Ident:
    error "cannot evaluate undeclared ident: " & pool.strings[n.litId], n.info
    inc n
  of Symbol:
    case n.symKind
    of ConstY, EfldY:
      let sym = tryLoadSym(n.symId)
      if sym.status == LacksNothing:
        result = asLocal(sym.decl).val
        inc n
        return
    else: discard
    error "cannot evaluate symbol at compile time: " & pool.syms[n.symId], n.info
    inc n
  of StringLit, CharLit, IntLit, UIntLit, FloatLit:
    result = n
    inc n
  of ParLe:
    case n.exprKind
    of TrueX, FalseX:
      result = n
      skip n
    of AndX:
      inc n
      let a = propagateError eval(c, n)
      if a.exprKind == FalseX:
        skipToEnd n
        return a
      elif a.exprKind != TrueX:
        error "expected bool for operand of `and` but got: " & toString(a, false), n.info
        return
      let b = propagateError eval(c, n)
      if not isConstBoolValue(b):
        error "expected bool for operand of `and` but got: " & toString(b, false), n.info
        return
      else:
        skipParRi n
        return b
    of OrX:
      inc n
      let a = propagateError eval(c, n)
      if a.exprKind == TrueX:
        skipToEnd n
        return a
      elif a.exprKind != FalseX:
        error "expected bool for operand of `or` but got: " & toString(a, false), n.info
        return
      let b = propagateError eval(c, n)
      if not isConstBoolValue(b):
        error "expected bool for operand of `or` but got: " & toString(b, false), n.info
        return
      else:
        skipParRi n
        return b
    of NotX:
      inc n
      let a = propagateError eval(c, n)
      if a.exprKind == TrueX:
        skipParRi n
        return c.getFalseValue()
      elif a.exprKind == FalseX:
        skipParRi n
        return c.getTrueValue()
      else:
        error "expected bool for operand of `not` but got: " & toString(a, false), n.info
        return
    of SufX:
      # we only need raw value
      inc n
      result = n
      skipToEnd n
    else:
      if n.tagId == ErrT:
        result = n
        skip n
      else:
        error "cannot evaluate expression at compile time: " & toString(n, false), n.info
  else:
    error "cannot evaluate expression at compile time: " & toString(n, false), n.info

proc evalExpr*(n: var Cursor): TokenBuf =
  var ec = initEvalContext()
  let val = eval(ec, n)
  result = createTokenBuf(val.span)
  result.addSubtree val

proc evalOrdinal*(n: Cursor): xint =
  var ec = initEvalContext()
  var n0 = n
  let val = eval(ec, n0)
  case val.kind
  of CharLit:
    result = createXint val.uoperand
  of IntLit:
    result = createXint pool.integers[val.intId]
  of UIntLit:
    result = createXint pool.uintegers[val.uintId]
  else:
    result = createNaN()
