#
#
#           NIFC Compiler
#        (c) Copyright 2024 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# We produce PreASM code as a list of NIF tokens.

import std / [assertions, syncio, tables, sets, intsets, strutils]
from std / os import changeFileExt, splitFile, extractFileName

import .. / .. / lib / [bitabs, packedtrees, lineinfos, nifstreams, nifcursors]
import .. / nifc_model
import preasm_model

type
  AsmTypeKind = enum
    ABool, # also useful for modelling CPU flag registers
    AInt, AUInt, AFloat, AMem
  AsmSlot = object
    kind: AsmTypeKind
    size, align, offset: int # offset is only used for fields and not
                             # really part of a "type" but it's easier this way

type
  GeneratedCode* = object
    m: Module
    data: TokenBuf
    code: TokenBuf
    init: TokenBuf
    inSimpleInit: int
    intmSize: int
    generatedTypes: IntSet
    requestedSyms: HashSet[string]
    fields: Table[LitId, AsmSlot]
    types: Table[LitId, AsmSlot]

  LitId = nifc_model.StrId

proc initGeneratedCode*(m: sink Module; intmSize: int): GeneratedCode =
  result = GeneratedCode(m: m, intmSize: intmSize)

proc add*[T](c: var GeneratedCode; x: T) {.inline.} =
  c.code.add x

proc error(m: Module; msg: string; tree: PackedTree[NifcKind]; n: NodePos) =
  write stdout, "[Error] "
  write stdout, msg
  writeLine stdout, toString(tree, n, m)
  quit 1

# Atoms

proc genIntLit(c: var GeneratedCode; litId: LitId; info: PackedLineInfo) =
  let i = parseBiggestInt(c.m.lits.strings[litId])
  let id = pool.integers.getOrIncl(i)
  c.code.add toToken(IntLit, id, info)

proc genIntLit(c: var GeneratedCode; i: BiggestInt; info: PackedLineInfo) =
  let id = pool.integers.getOrIncl(i)
  c.code.add toToken(IntLit, id, info)

proc genUIntLit(c: var GeneratedCode; litId: LitId; info: PackedLineInfo) =
  let i = parseBiggestUInt(c.m.lits.strings[litId])
  let id = pool.uintegers.getOrIncl(i)
  c.code.add toToken(UIntLit, id, info)

proc addIdent(c: var GeneratedCode; s: string; info: PackedLineInfo) =
  c.code.add toToken(Ident, pool.strings.getOrIncl(s), info)

proc addEmpty(c: var GeneratedCode; info: PackedLineInfo) =
  c.code.add toToken(DotToken, 0'u32, info)

proc addKeyw(c: var GeneratedCode; keyw: TagId; info: PackedLineInfo) =
  c.code.buildTree keyw, info: discard

proc addSymDef(c: var GeneratedCode; s: string; info: PackedLineInfo) =
  c.code.add toToken(SymbolDef, pool.syms.getOrIncl(s), info)

proc addSym(c: var GeneratedCode; s: string; info: PackedLineInfo) =
  c.code.add toToken(Symbol, pool.syms.getOrIncl(s), info)

template buildTree(c: var GeneratedCode; keyw: TagId; info: PackedLineInfo; body: untyped) =
  c.code.buildTree keyw, info:
    body

# Type graph

include genpreasm_t

# Procs

type
  ProcFlag = enum
    isSelectAny, isVarargs

proc genProcPragmas(c: var GeneratedCode; t: Tree; n: NodePos;
                    flags: var set[ProcFlag]) =
  # ProcPragma ::= (inline) | (noinline) | CallingConvention | (varargs) | (was Identifier) |
  #               (selectany) | Attribute
  if t[n].kind == Empty:
    discard
  elif t[n].kind == PragmasC:
    for ch in sons(t, n):
      case t[ch].kind
      of CallingConventions:
        c.addIdent $t[ch].kind, t[n].info
      of VarargsC:
        flags.incl isVarargs
      of SelectanyC:
        flags.incl isSelectAny
      of InlineC, AttrC, NoinlineC:
        # Ignore for PreASM
        discard " __attribute__((noinline))"
      of WasC: genWas(c, t, ch)
      else:
        error c.m, "invalid proc pragma: ", t, ch
  else:
    error c.m, "expected proc pragmas but got: ", t, n

proc genSymDef(c: var GeneratedCode; t: Tree; n: NodePos): string =
  if t[n].kind == SymDef:
    let lit = t[n].litId
    result = c.m.lits.strings[lit]
    c.addSymDef result, t[n].info
  else:
    error c.m, "expected SymbolDef but got: ", t, n
    result = ""

proc genParamPragmas(c: var GeneratedCode; t: Tree; n: NodePos) =
  # ProcPragma ::= (was Identifier) | Attribute
  if t[n].kind == Empty:
    c.addEmpty t[n].info
  elif t[n].kind == PragmasC:
    for ch in sons(t, n):
      case t[ch].kind
      of AttrC:
        discard "Ignore for now"
      of WasC:
        genWas c, t, ch
      else:
        error c.m, "invalid pragma: ", t, ch
  else:
    error c.m, "expected pragmas but got: ", t, n

proc genParam(c: var GeneratedCode; t: Tree; n: NodePos) =
  let d = asParamDecl(t, n)
  if t[d.name].kind == SymDef:
    let lit = t[d.name].litId
    let name = mangle(c.m.lits.strings[lit])
    genType c, t, d.typ, name
    genParamPragmas c, t, d.pragmas
  else:
    error c.m, "expected SymbolDef but got: ", t, n

proc genVarPragmas(c: var GeneratedCode; t: Tree; n: NodePos) =
  if t[n].kind == Empty:
    discard
  elif t[n].kind == PragmasC:
    for ch in sons(t, n):
      case t[ch].kind
      of AlignC:
        c.add " NIM_ALIGN(" & toString(t, ch.firstSon, c.m) & ")"
      of AttrC:
        c.add " __attribute__((" & toString(t, ch.firstSon, c.m) & "))"
      of WasC:
        genWas c, t, ch
      else:
        error c.m, "invalid pragma: ", t, ch
  else:
    error c.m, "expected pragmas but got: ", t, n

include genpreasm_e

type
  VarKind = enum
    IsLocal, IsGlobal, IsThreadlocal, IsConst

proc genVarDecl(c: var GeneratedCode; t: Tree; n: NodePos; vk: VarKind) =
  let d = asVarDecl(t, n)
  if t[d.name].kind == SymDef:
    let lit = t[d.name].litId
    let name = mangle(c.m.lits.strings[lit])
    if vk == IsConst:
      c.add ConstKeyword
    genType c, t, d.typ, name
    if vk == IsThreadlocal:
      c.add " __thread"
    genVarPragmas c, t, d.pragmas
    if t[d.value].kind != Empty:
      c.add AsgnOpr
      if vk != IsLocal: inc c.inSimpleInit
      genx c, t, d.value
      if vk != IsLocal: dec c.inSimpleInit
    c.add Semicolon
  else:
    error c.m, "expected SymbolDef but got: ", t, n

template moveToDataSection(body: untyped) =
  let oldLen = c.code.len
  body
  for i in oldLen ..< c.code.len:
    c.data.add c.code[i]
  setLen c.code, oldLen

include genpreasm_t

proc genProcDecl(c: var GeneratedCode; t: Tree; n: NodePos; isExtern: bool) =
  let signatureBegin = c.code.len
  let prc = asProcDecl(t, n)

  if isExtern:
    c.add ExternKeyword

  genType c, t, prc.returnType
  c.add Space
  let name = genSymDef(c, t, prc.name)

  var flags: set[ProcFlag] = {}
  genProcPragmas c, t, prc.pragmas, flags

  c.add ParLe

  var params = 0
  if t[prc.params].kind != Empty:
    for ch in sons(t, prc.params):
      if params > 0: c.add Comma
      genParam c, t, ch
      inc params

  if isVarargs in flags:
    if params > 0: c.add Comma
    c.add "..."
    inc params

  if params == 0:
    c.add "void"
  c.add ParRi

  if isExtern or c.requestedSyms.contains(name):
    # symbol was used before its declaration has been processed so
    # add a signature:
    for i in signatureBegin ..< c.code.len:
      c.protos.add c.code[i]
    c.protos.add Token Semicolon

  if isExtern:
    c.code.setLen signatureBegin
  else:
    if isSelectAny in flags:
      genRoutineGuardBegin(c, name)
    c.add CurlyLe
    genStmt c, t, prc.body
    c.add CurlyRi
    if isSelectAny in flags:
      genRoutineGuardEnd(c)

proc genImp(c: var GeneratedCode; t: Tree; n: NodePos) =
  c.add ExternKeyword
  let arg = n.firstSon
  case t[arg].kind
  of ProcC: genProcDecl c, t, arg, true
  of VarC: genStmt c, t, arg
  of ConstC: genStmt c, t, arg
  else:
    error c.m, "expected declaration for `imp` but got: ", t, n

proc genToplevel(c: var GeneratedCode; t: Tree; n: NodePos) =
  # ExternDecl ::= (imp ProcDecl | VarDecl | ConstDecl)
  # Include ::= (incl StringLiteral)
  # TopLevelConstruct ::= ExternDecl | ProcDecl | VarDecl | ConstDecl |
  #                       TypeDecl | Include | EmitStmt
  case t[n].kind
  of ImpC: genImp c, t, n
  of NodeclC: discard "Ignore nodecl"
  of InclC: genInclude c, t, n
  of ProcC: genProcDecl c, t, n, false
  of VarC: genStmt c, t, n
  of ConstC: genStmt c, t, n
  of TypeC: discard "handled in a different pass"
  of EmitC: genEmitStmt c, t, n
  else:
    error c.m, "expected top level construct but got: ", t, n

proc traverseCode(c: var GeneratedCode; t: Tree; n: NodePos) =
  case t[n].kind
  of StmtsC:
    for ch in sons(t, n): genToplevel(c, t, ch)
  else:
    error c.m, "expected `stmts` but got: ", t, n

proc generatePreAsm*(inp, outp: string; intmSize: int) =
  var c = initGeneratedCode(load(inp), intmSize)

  var co = TypeOrder()
  traverseTypes(c.m, co)

  generateTypes(c, c.m.types, co)

  traverseCode c, c.m.code, StartPos
  var f = CppFile(f: open(outp, fmWrite))
  f.write "#define NIM_INTBITS " & $intmSize & "\n"
  writeTokenSeq f, c.data, c
  writeTokenSeq f, c.protos, c
  writeTokenSeq f, c.code, c
  if c.init.len > 0:
    f.write "void __attribute__((constructor)) init(void) {"
    writeTokenSeq f, c.init, c
    f.write "}\n\n"
  f.f.close
