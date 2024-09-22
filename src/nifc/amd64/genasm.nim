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
import ".." / [nifc_model, typenav]
import ".." / native / [slots, analyser]
import asm_model, machine, emitter

type
  Label = distinct int
  TempVar = distinct int

type
  Scope = object
    # usedRegisters: RegisterSet # XXX later once we have a `frame` abstraction
    # usedMem: (int, int)
    syms: Table[LitId, AsmSlot]
  GeneratedCode* = object
    m: Module
    rodata, data: TokenBuf
    code: TokenBuf
    init: TokenBuf
    rega: RegAllocator
    intmSize, inConst, labels, temps: int
    loopExits: seq[Label]
    generatedTypes: IntSet
    requestedSyms: HashSet[string]
    fields: Table[LitId, AsmSlot]
    types: Table[LitId, AsmSlot]
    locals: Table[LitId, Location]
    strings: Table[string, int]
    scopes: seq[Scope]
    returnSlot: AsmSlot
    returnLoc: Location
    threadLocalsSize, globalsSize: int
    globals: Table[LitId, AsmSlot]

  LitId = nifc_model.StrId

proc openScope(c: var GeneratedCode) =
  c.scopes.add Scope()

proc closeScope(c: var GeneratedCode) =
  discard c.scopes.pop()

proc initGeneratedCode*(m: sink Module; intmSize: int): GeneratedCode =
  result = GeneratedCode(m: m, intmSize: intmSize)

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

proc genFloatLit(c: var GeneratedCode; litId: LitId; info: PackedLineInfo) =
  let i = parseFloat(c.m.lits.strings[litId])
  let id = pool.floats.getOrIncl(i)
  c.code.add toToken(FloatLit, id, info)

proc genCharLit(c: var GeneratedCode; ch: char; info: PackedLineInfo) =
  c.code.add toToken(CharLit, uint32(ch), info)

proc addIdent(c: var GeneratedCode; s: string; info: PackedLineInfo) =
  c.code.add toToken(Ident, pool.strings.getOrIncl(s), info)

proc addEmpty(c: var GeneratedCode; info: PackedLineInfo) =
  c.code.add toToken(DotToken, 0'u32, info)

proc addKeyw(c: var GeneratedCode; keyw: TagId; info = NoLineInfo) =
  c.code.buildTree keyw, info: discard

proc addKeywUnchecked(c: var GeneratedCode; keyw: string; info = NoLineInfo) =
  c.code.buildTree pool.tags.getOrIncl(keyw), info: discard

proc addSymDef(c: var TokenBuf; s: string; info: PackedLineInfo) =
  c.add toToken(SymbolDef, pool.syms.getOrIncl(s), info)

proc addStrLit(c: var TokenBuf; s: string; info: PackedLineInfo) =
  c.add toToken(StringLit, pool.strings.getOrIncl(s), info)

proc addSym(c: var GeneratedCode; s: string; info: PackedLineInfo) =
  c.code.add toToken(Symbol, pool.syms.getOrIncl(s), info)

proc getLabel(c: var GeneratedCode): Label =
  result = Label(c.labels)
  inc c.labels

proc getTempVar(c: var GeneratedCode): TempVar =
  result = TempVar(c.temps)
  inc c.temps

proc defineLabel(c: var GeneratedCode; lab: Label; info: PackedLineInfo) =
  c.code.addSymDef "L." & $int(lab), info

proc useLabel(c: var GeneratedCode; lab: Label; info: PackedLineInfo) =
  c.addSym "L." & $int(lab), info

proc defineTemp(c: var GeneratedCode; tmp: TempVar; info: PackedLineInfo) =
  c.code.addSymDef "v." & $int(tmp), info

proc useTemp(c: var GeneratedCode; tmp: TempVar; info: PackedLineInfo) =
  c.addSym "v." & $int(tmp), info

template buildTree(c: var GeneratedCode; keyw: TagId; body: untyped) =
  c.code.buildTree keyw, NoLineInfo:
    body

template buildTreeI(c: var GeneratedCode; keyw: TagId; info: PackedLineInfo; body: untyped) =
  c.code.buildTree keyw, info:
    body

# Type graph

include ".." / preasm / genpreasm_t

# Procs

proc genWas(c: var GeneratedCode; t: Tree; ch: NodePos) =
  c.code.buildTree(CommentT, t[ch].info):
    c.code.add toToken(Ident, pool.strings.getOrIncl(toString(t, ch.firstSon, c.m)), t[ch].info)

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
      of CdeclC, StdcallC, NoconvC: discard "supported calling convention"
      of SafecallC, SyscallC, FastcallC, ThiscallC, MemberC:
        error c.m, "unsupported calling convention: ", t, ch
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
    c.code.addSymDef result, t[n].info
  else:
    error c.m, "expected SymbolDef but got: ", t, n
    result = ""

proc genParamPragmas(c: var GeneratedCode; t: Tree; n: NodePos) =
  # ProcPragma ::= (was Identifier) | Attribute
  if t[n].kind == Empty:
    discard
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

proc genVarPragmas(c: var GeneratedCode; t: Tree; n: NodePos; alignOverride: var int) =
  if t[n].kind == Empty:
    discard
  elif t[n].kind == PragmasC:
    for ch in sons(t, n):
      case t[ch].kind
      of AlignC:
        let intId = t[ch.firstSon].litId
        alignOverride = parseInt(c.m.lits.strings[intId])
      of AttrC:
        discard "ignore attribute"
      of WasC:
        genWas c, t, ch
      else:
        error c.m, "invalid pragma: ", t, ch
  else:
    error c.m, "expected pragmas but got: ", t, n

include genasm_e

type
  VarKind = enum
    IsLocal, IsGlobal, IsThreadlocal

proc allocGlobal(size: var int; dest: var AsmSlot) =
  size = align(size, dest.align)
  dest.offset = size
  inc size, dest.size

proc genVarDecl(c: var GeneratedCode; t: Tree; n: NodePos; vk: VarKind) =
  let d = asVarDecl(t, n)
  if t[d.name].kind == SymDef:
    let lit = t[d.name].litId
    let name = c.m.lits.strings[lit]
    let opc =
      case vk
      of IsLocal: VarT
      of IsGlobal: GvarT
      of IsThreadlocal: TvarT
    c.buildTreeI opc, t[n].info:
      c.code.addSymDef name, t[d.name].info
      var alignOverride = -1
      genVarPragmas c, t, d.pragmas, alignOverride

      # genType inlined:
      var dest = AsmSlot()
      fillTypeSlot c, typeFromPos(n), dest
      if alignOverride >= 0:
        dest.align = alignOverride
      genSlot c, dest, c.m.code[n].info
    case vk
    of IsLocal:
      c.scopes[c.scopes.high].syms[name] = dest
    of IsGlobal:
      allocGlobal c.globalsSize, dest
      c.globals[name] = dest
    of IsThreadlocal:
      allocGlobal c.threadLocalsSize, dest
      c.globals[name] = dest

    if t[d.value].kind != Empty:
      c.buildTreeI AsgnT, t[d.value].info:
        genType c, d.typ, alignOverride
        c.addSym name, t[d.name].info
        genx c, t, d.value, WantValue
  else:
    error c.m, "expected SymbolDef but got: ", t, n

proc genConstDecl(c: var GeneratedCode; t: Tree; n: NodePos) =
  let d = asVarDecl(t, n)
  if t[d.name].kind == SymDef:
    let lit = t[d.name].litId
    let name = c.m.lits.strings[lit]

    c.buildTreeI ConstT, t[n].info:
      c.code.addSymDef name, t[d.name].info
      var alignOverride = -1
      genVarPragmas c, t, d.pragmas, alignOverride
      genType c, d.typ, alignOverride

      if t[d.value].kind != Empty:
        c.buildTree ValuesT, t[d.value].info:
          inc c.inConst
          genx c, t, d.value, WantValue
          dec c.inConst
      else:
        error c.m, "const needs a value: ", t, n
  else:
    error c.m, "expected SymbolDef but got: ", t, n

template moveToDataSection(body: untyped) =
  let oldLen = c.code.len
  body
  for i in oldLen ..< c.code.len:
    c.data.add c.code[i]
  shrink c.code, oldLen

include genasm_s

proc genProcDecl(c: var GeneratedCode; t: Tree; n: NodePos) =
  c.labels = 0 # reset so that we produce nicer code
  c.temps = 0
  let prc = asProcDecl(t, n)
  if t[prc.body].kind == Empty: return # ignore procs without body
  # (proc SYMBOLDEF Params Type ProcPragmas (OR . StmtList)
  c.openScope() # open scope for the parameters
  c.rega = initRegAllocator()
  c.buildTreeI ProcT, t[n].info:
    discard genSymDef(c, t, prc.name)

    if t[prc.returnType].kind != VoidC:
      c.returnSlot = typeToSlot(c, prc.returnType)
      allocResultWin64 c.rega, c.returnSlot, c.returnLoc

    if t[prc.params].kind != Empty:
      var paramTypes: seq[AsmSlot] = @[]
      var paramLocs: seq[Location] = @[]
      for ch in sons(t, prc.params):
        let d = asParamDecl(t, n)
        if t[d.name].kind == SymDef:
          paramTypes.add typeToSlot(c, d.typ)
          paramLocs.add Location(kind: DontCare)
        else:
          error c.m, "expected SymbolDef but got: ", t, n
      allocParamsWin64 c.rega, paramTypes, paramLocs
      var i = 0
      for ch in sons(t, prc.params):
        let d = asParamDecl(t, n)
        if t[d.name].kind == SymDef:
          let lit = t[d.name].litId
          c.scopes[^1].syms[lit] = paramLocs[i]
          inc i

    var flags: set[ProcFlag] = {}
    genProcPragmas c, t, prc.pragmas, flags
    genStmt c, t, prc.body
  c.closeScope() # close parameter scope

proc genToplevel(c: var GeneratedCode; t: Tree; n: NodePos) =
  # ExternDecl ::= (imp ProcDecl | VarDecl | ConstDecl)
  # Include ::= (incl StringLiteral)
  # TopLevelConstruct ::= ExternDecl | ProcDecl | VarDecl | ConstDecl |
  #                       TypeDecl | Include | EmitStmt
  case t[n].kind
  of ImpC: discard "ignore imp"
  of NodeclC: discard "ignore nodecl"
  of InclC: discard "genInclude c, t, n"
  of ProcC: genProcDecl c, t, n
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

proc generateAsm*(inp, outp: string) =
  registerTags()
  var c = initGeneratedCode(load(inp), 8)

  var co = TypeOrder()
  traverseTypes(c.m, co)

  generateTypes(c, co)

  traverseCode c, c.m.code, StartPos
  var f = open(outp, fmWrite)
  f.write "(.nif24)\n(stmts"
  f.write toString(c.data)
  f.write toString(c.code)
  f.write ")\n"
  if c.init.len > 0:
    quit "no init code implemented"
  f.close
