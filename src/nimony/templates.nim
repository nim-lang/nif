#       Nimony Compiler
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## This module implements the template expansion mechanism.

import std / tables

import nifreader, nifstreams, nifcursors, decls, programs
import ".." / specs / tags

type
  ExpansionContext = object
    newVars: Table[SymId, SymId]
    formalParams, typevars: Table[SymId, Cursor]
    firstVarargMatch: Cursor

proc expandTemplateImpl(dest: var TokenBuf; c: var ExpansionContext; body: Cursor;
                        inferred: Table[SymId, Cursor]) =
  var nested = 0
  var body = body
  while true:
    case body.kind
    of UnknownToken, EofToken, DotToken, Ident:
      dest.add body
    of Symbol:
      let s = body.symId
      let arg = c.formalParams.getOrDefault(s)
      if arg != default(Cursor):
        dest.addSubtree arg
      else:
        let nv = c.newVars.getOrDefault(s)
        if nv != SymId(0):
          dest.add toToken(Symbol, nv, body.info)
        else:
          let tv = inferred.getOrDefault(s)
          if tv != default(Cursor):
            dest.addSubtree tv
          else:
            dest.add body # keep Symbol as it was
    of SymbolDef:
      let s = body.symId
      let newDef = freshSym(s)
      c.newVars[s] = newDef
      dest.add toToken(SymbolDef, newDef, body.info)
    of StringLit, CharLit, IntLit, UIntLit, FloatLit:
      dest.add body
    of ParLe:
      let forStmt = asForStmt(body)
      if forStmt.tag == ForT and forStmt.iter.tag == UnpackT:
        assert forStmt.vars.tag == UnpackIntoFlatT
        var arg = c.firstVarargMatch
        var fv = forStmt.vars
        inc fv
        inc fv
        let vid = fv.symId
        if arg.kind notin {DotToken, ParRi}:
          while arg.kind != ParRi:
            c.formalParams[vid] = arg
            expandTemplateImpl dest, c, forStmt.body, inferred
            skip arg

        skip body
        unsafeDec body
      else:
        inc nested
    of ParRi:
      dest.add body
      if nested == 0: break
    inc body

proc expandTemplate*(dest: var TokenBuf; templateDecl, args, firstVarargMatch: Cursor;
                    inferred: Table[SymId, Cursor]) =
  var templ = asRoutine(templateDecl)

  var c = ExpansionContext(
    newVars: initTable[SymId, SymId](),
    formalParams: initTable[SymId, Cursor](),
    firstVarargMatch: firstVarargMatch)

  var a = args
  var f = templ.params
  if f.kind != DotToken:
    while f.kind != ParRi and a.kind != ParRi:
      var param = f
      inc param
      assert param.kind == SymbolDef
      c.formalParams[param.symId] = a
      skip a
      skip f

  expandTemplateImpl dest, c, templ.body, inferred
