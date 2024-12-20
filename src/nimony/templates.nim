#       Nimony Compiler
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## This module implements the template expansion mechanism.

# included from sem.nim

type
  ExpansionContext = object
    newVars: Table[SymId, SymId]
    formalParams, typevars: Table[SymId, Cursor]
    firstVarargMatch: Cursor
    inferred: ptr Table[SymId, Cursor]

proc expandTemplateImpl(c: var SemContext; dest: var TokenBuf;
                        e: var ExpansionContext; body: Cursor) =
  var nested = 0
  var body = body
  let isAtom = body.kind != ParLe
  while true:
    case body.kind
    of UnknownToken, EofToken, DotToken, Ident:
      dest.add body
    of Symbol:
      let s = body.symId
      let arg = e.formalParams.getOrDefault(s)
      if arg != default(Cursor):
        dest.addSubtree arg
      else:
        let nv = e.newVars.getOrDefault(s)
        if nv != SymId(0):
          dest.add symToken(nv, body.info)
        else:
          let tv = e.inferred[].getOrDefault(s)
          if tv != default(Cursor):
            dest.addSubtree tv
          else:
            dest.add body # keep Symbol as it was
    of SymbolDef:
      let s = body.symId
      let newDef = newSymId(c, s)
      e.newVars[s] = newDef
      dest.add symdefToken(newDef, body.info)
    of StringLit, CharLit, IntLit, UIntLit, FloatLit:
      dest.add body
    of ParLe:
      let forStmt = asForStmt(body)
      if forStmt.kind == ForS and forStmt.iter.exprKind == UnpackX:
        assert forStmt.vars.substructureKind == UnpackFlatS
        var arg = e.firstVarargMatch
        var fv = forStmt.vars
        inc fv
        inc fv
        let vid = fv.symId
        if arg.kind notin {DotToken, ParRi}:
          while arg.kind != ParRi:
            e.formalParams[vid] = arg
            expandTemplateImpl c, dest, e, forStmt.body
            skip arg

        skip body
        unsafeDec body
      elif body.exprKind == UnpackX:
        inc body
        var arg = e.firstVarargMatch
        if body.kind == ParRi:
          # `unpack()` variant:
          while arg.kind != ParRi:
            dest.takeTree arg
        else:
          # `unpack(fn)` variant:
          while arg.kind != ParRi:
            dest.addParLe CallX, arg.info
            dest.copyTree body # fn
            dest.takeTree arg
            dest.addParRi()
          skip body
          unsafeDec body
      else:
        dest.add body
        inc nested
    of ParRi:
      dest.add body
      dec nested
      if nested == 0: break
    if isAtom: break
    inc body

proc expandTemplate*(c: var SemContext; dest: var TokenBuf;
                     templateDecl, args, firstVarargMatch: Cursor;
                     inferred: ptr Table[SymId, Cursor]) =
  var templ = asRoutine(templateDecl)

  var e = ExpansionContext(
    newVars: initTable[SymId, SymId](),
    formalParams: initTable[SymId, Cursor](),
    firstVarargMatch: firstVarargMatch,
    inferred: inferred)

  var a = args
  var f = templ.params
  if f.kind != DotToken:
    assert f == "params"
    inc f
    while f.kind != ParRi and a.kind != ParRi:
      var param = f
      inc param
      assert param.kind == SymbolDef
      e.formalParams[param.symId] = a
      skip a
      skip f

  expandTemplateImpl c, dest, e, templ.body
