#       Nimony
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Semantic checking:
## Most important task is to turn identifiers into symbols and to perform
## type checking.

import std / [tables, os, syncio]
include nifprelude
import nimony_model, symtabs, builtintypes, decls,
  programs, sigmatch

type
  SemRoutine* {.acyclic.} = ref object
    kind: StmtKind
    up: SemRoutine

  SemContext* = object
    r: SemRoutine
    currentScope: Scope
    dest: TokenBuf
    nestedIn: seq[(StmtKind, SymId)]
    types: BuiltinTypes

proc openScope(s: var SemContext) =
  s.currentScope = Scope(tab: initTable[StrId, seq[Sym]](), up: s.currentScope, kind: NormalScope)

proc closeScope(s: var SemContext) =
  s.currentScope = s.currentScope.up

proc buildErr*(c: var SemContext; info: PackedLineInfo; msg: string) =
  c.dest.buildTree ErrT, info:
    c.dest.add toToken(StringLit, pool.strings.getOrIncl(msg), info)

proc typeToString(e: var SemContext; c: Cursor): string =
  result = toString(c)

proc wantParRi(e: var SemContext; c: var Cursor) =
  if c.kind == ParRi:
    e.dest.add c
    inc c
  else:
    error "expected ')', but got: ", c

proc skipParRi(e: var SemContext; c: var Cursor) =
  if c.kind == ParRi:
    inc c
  else:
    error "expected ')', but got: ", c

proc takeToken(e: var SemContext; c: var Cursor) {.inline.} =
  e.dest.add c
  inc c

proc semExpr(e: var SemContext; it: var Item)

proc classifyType(e: var SemContext; c: Cursor): TypeKind =
  result = typeKind(c)

proc semBoolExpr(e: var SemContext; it: var Item) =
  semExpr e, it
  if typeKind(it.typ) != BoolT:
    buildErr e, it.n.info, "expected `bool` but got: " & typeToString(e, it.typ)

proc semStmt(e: var SemContext; c: var Cursor) =
  var it = Item(n: c, typ: e.types.autoType)
  semExpr e, it
  if classifyType(e, it.typ) in {NoType, VoidT}:
    discard "ok"
  else:
    buildErr e, c.info, "expression of type `" & typeToString(e, it.typ) & "` must be discarded"
  c = it.n

proc semCall(e: var SemContext; it: var Item) =
  var dest = createTokenBuf(16)
  swap e.dest, dest
  var fn = Item(n: it.n, typ: e.types.autoType)
  semExpr e, fn
  let firstArg = fn.n
  it.n = fn.n
  while it.n.kind != ParRi:
    semExpr e, it
  wantParRi e, it.n

  swap e.dest, dest

  e.dest.add dest


proc semExpr(e: var SemContext; it: var Item) =
  case it.n.kind
  of IntLit:
    if typeKind(it.typ) == AutoT:
      it.typ = e.types.intType
    takeToken e, it.n
  of UIntLit:
    if typeKind(it.typ) == AutoT:
      it.typ = e.types.uintType
    takeToken e, it.n
  of FloatLit:
    if typeKind(it.typ) == AutoT:
      it.typ = e.types.floatType
    takeToken e, it.n
  of StringLit:
    if typeKind(it.typ) == AutoT:
      it.typ = e.types.stringType
    takeToken e, it.n
  of CharLit:
    if typeKind(it.typ) == AutoT:
      it.typ = e.types.charType
    takeToken e, it.n
  of Symbol, Ident:
    buildErr e, it.n.info, "not implemented"
  of ParLe:
    case exprKind(it.n)
    of NoExpr:
      buildErr e, it.n.info, "expression expected"
    of FalseX, TrueX:
      if typeKind(it.typ) == AutoT:
        it.typ = e.types.boolType
      takeToken e, it.n
      wantParRi e, it.n
    of InfX, NegInfX, NanX:
      if typeKind(it.typ) == AutoT:
        it.typ = e.types.floatType
      takeToken e, it.n
      wantParRi e, it.n
    of AndX, OrX:
      takeToken e, it.n
      semBoolExpr e, it
      semBoolExpr e, it
      wantParRi e, it.n
    of NotX:
      e.dest.add it.n
      takeToken e, it.n
      semBoolExpr e, it
      wantParRi e, it.n
    of ParX:
      takeToken e, it.n
      semExpr e, it
      wantParRi e, it.n
    of CallX:
      semCall e, it
    of AconstrX, AtX, DerefX, DotX, PatX, AddrX, NilX, NegX, SizeofX, OconstrX, KvX,
       AddX, SubX, MulX, DivX, ModX, ShrX, ShlX, BitandX, BitorX, BitxorX, BitnotX,
       EqX, NeqX, LeX, LtX, CastX, ConvX, SufX, RangeX, RangesX,
       HderefX, HaddrX, OconvX, HconvX:
      takeToken e, it.n
      wantParRi e, it.n

  of ParRi, EofToken, SymbolDef, UnknownToken, DotToken:
    buildErr e, it.n.info, "expression expected"

proc writeOutput(e: var SemContext; outfile: string) =
  #var b = nifbuilder.open(outfile)
  #b.addHeader "nimony", "nim-sem"
  #b.addRaw toString(e.dest)
  #b.close()
  writeFile outfile, "(.nif42)\n" & toString(e.dest)

proc semcheck*(infile, outfile: string) =
  var c = setupProgram(infile)
  var e = SemContext(
    dest: createTokenBuf(),
    nestedIn: @[(StmtsS, SymId(0))],
    types: createBuiltinTypes())
  e.currentScope = Scope(tab: initTable[StrId, seq[Sym]](), up: nil, kind: ToplevelScope)

  semStmt e, c
  if c.kind != EofToken:
    quit "Internal error: file not processed completely"
  # fix point: generic instantiations:
  when false:
    var i = 0
    while i < e.requires.len:
      let imp = e.requires[i]
      if not e.declared.contains(imp):
        importSymbol(e, imp)
      inc i
  writeOutput e, outfile

