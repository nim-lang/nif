#       Nimony
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Implements the transformation that the `.borrow` pragma requires.

import std / [tables, sets, syncio, formatfloat, assertions]
include nifprelude
import nimony_model, symtabs, builtintypes, decls, symparser,
  programs, sigmatch, magics, reporters,
  semdata, sembasics

proc skipDistinct*(n: TypeCursor; isDistinct: var bool): TypeCursor =
  # XXX Consider generic types here and construct `DistinctType[Params...]` for these!
  var n = n
  var i = 0
  while i < 10:
    n = skipModifier(n)
    if n.kind == Symbol:
      let section = getTypeSection(n.symId)
      if section.kind == TypeY:
        n = section.body
        if n.typeKind == DistinctT:
          isDistinct = true
          inc n
      inc i
    else:
      break
  result = n

proc genBorrowedProcBody*(c: var SemContext; fn: StrId; signature: Cursor; info: PackedLineInfo): TokenBuf =
  #[

  Consider:

  type
    VarId* = distinct int

  proc `+`*(x, y: VarId): VarId {.borrow.}

  Implementation: Generate a body for this proc in phase 3.
  The body is a single call of the current proc name, converted
  to the distinct type, if the return type is one. The type could also
  be generic, so generate the parmeter type properly. It also needs to
  skip modifiers first.

  ]#
  var n = signature
  assert n == $ParamsS
  inc n
  result = createTokenBuf(10)
  result.add parLeToken(StmtsS, info)
  result.add parLeToken(CallS, info)
  result.add identToken(fn, info)
  var distinctParams = 0
  while n.kind != ParRi:
    let param = asLocal(n)
    if param.kind == ParamY and param.name.kind == SymbolDef:
      var isDistinct = false
      let destType = skipDistinct(param.typ, isDistinct)
      if isDistinct:
        result.add parLeToken(DconvX, info)
        result.copyTree destType
        result.add symToken(param.name.symId, info)
        result.add parRiToken(info)
        inc distinctParams
      else:
        result.add symToken(param.name.symId, info)
    skip n

  if n.kind == DotToken:
    discard "fine: no return type"
  else:
    var isDistinct = false
    discard skipDistinct(n, isDistinct)
    if isDistinct:
      var finalConv = createTokenBuf(4)
      finalConv.add parLeToken(DconvX, info)
      finalConv.copyTree n
      result.insert finalConv, 1
      result.add parRiToken(info)

  result.add parRiToken(info)
  result.add parRiToken(info)
  if distinctParams == 0:
    result.shrink 0
    result.buildLocalErr info, "cannot .borrow: no parameter of a `distinct` type"
