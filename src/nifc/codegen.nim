#
#
#           NIFC Compiler
#        (c) Copyright 2024 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# We produce C code as a list of tokens.

import std / [assertions, syncio, tables, sets, intsets, formatfloat]
from std / strutils import parseBiggestInt, parseBiggestUInt, parseInt
from std / os import changeFileExt

import .. / lib / [bitabs, packedtrees]
import mangler, nifc_model, cprelude

type
  Token = distinct uint32

proc `==`(a, b: Token): bool {.borrow.}

type
  PredefinedToken = enum
    IgnoreMe = "<unused>"
    EmptyToken = ""
    CurlyLe = "{"
    CurlyRi = "}"
    ParLe = "("
    ParRi = ")"
    BracketLe = "["
    BracketRi = "]"
    NewLine = "\n"
    Semicolon = ";"
    Comma = ", "
    Space = " "
    Colon = ": "
    Dot = "."
    Arrow = "->"
    Star = "*"
    Amp = "&"
    AsgnOpr = " = "
    ScopeOpr = "::"
    ConstKeyword = "const "
    StaticKeyword = "static "
    ExternKeyword = "extern "
    WhileKeyword = "while "
    GotoKeyword = "goto "
    IfKeyword = "if ("
    ElseKeyword = "else "
    SwitchKeyword = "switch "
    CaseKeyword = "case "
    DefaultKeyword = "default:"
    BreakKeyword = "break"
    NullPtr = "nullptr"
    IfNot = "if (!("
    ReturnKeyword = "return "
    TypedefStruct = "typedef struct "
    TypedefUnion = "typedef union "
    IncludeKeyword = "#include "

proc fillTokenTable(tab: var BiTable[Token, string]) =
  for e in EmptyToken..high(PredefinedToken):
    let id = tab.getOrIncl $e
    assert id == Token(e), $(id, " ", ord(e))

type
  GeneratedCode* = object
    m: Module
    includes: seq[Token]
    includedHeaders: IntSet
    data: seq[Token]
    protos: seq[Token]
    code: seq[Token]
    init: seq[Token]
    tokens: BiTable[Token, string]
    headerFile: seq[Token]
    generatedTypes: IntSet
    requestedSyms: HashSet[string]

proc initGeneratedCode*(m: sink Module): GeneratedCode =
  result = GeneratedCode(m: m, code: @[], tokens: initBiTable[Token, string]())
  fillTokenTable(result.tokens)

proc add*(g: var GeneratedCode; t: PredefinedToken) {.inline.} =
  g.code.add Token(t)

proc add*(g: var GeneratedCode; s: string) {.inline.} =
  g.code.add g.tokens.getOrIncl(s)

type
  CppFile = object
    f: File

proc write(f: var CppFile; s: string) = write(f.f, s)
proc write(f: var CppFile; c: char) = write(f.f, c)

proc writeTokenSeq(f: var CppFile; s: seq[Token]; c: GeneratedCode) =
  var indent = 0
  for i in 0..<s.len:
    let x = s[i]
    case x
    of Token(CurlyLe):
      inc indent
      write f, c.tokens[x]
      write f, "\n"
      for i in 1..indent*2: write f, ' '
    of Token(CurlyRi):
      dec indent
      write f, c.tokens[x]
      if i+1 < s.len and s[i+1] == Token(CurlyRi):
        discard
      else:
        write f, "\n"
        for i in 1..indent*2: write f, ' '
    of Token(Semicolon):
      write f, c.tokens[x]
      if i+1 < s.len and s[i+1] == Token(CurlyRi):
        discard "no newline before }"
      else:
        write f, "\n"
        for i in 1..indent*2: write f, ' '
    of Token(NewLine):
      write f, c.tokens[x]
      for i in 1..indent*2: write f, ' '
    else:
      write f, c.tokens[x]

proc error(m: Module; msg: string; tree: PackedTree[NifcKind]; n: NodePos) =
  write stdout, "[Error] "
  write stdout, msg
  writeLine stdout, toString(tree, n, m)
  quit 1

# Atoms

proc genIntLit(c: var GeneratedCode; litId: StrId) =
  let i = parseBiggestInt(c.m.lits.strings[litId])
  if i > low(int32) and i <= high(int32):
    c.add $i
  elif i == low(int32):
    # Nim has the same bug for the same reasons :-)
    c.add "(-2147483647 -1)"
  elif i > low(int64):
    c.add "IL64("
    c.add $i
    c.add ")"
  else:
    c.add "(IL64(-9223372036854775807) - IL64(1))"

proc genUIntLit(c: var GeneratedCode; litId: StrId) =
  let i = parseBiggestUInt(c.m.lits.strings[litId])
  if i <= high(uint32):
    c.add $i
    c.add "u"
  else:
    c.add $i
    c.add "ull"

# Type graph

include gentypes

# Procs

template emitData(s: string) = c.data.add c.tokens.getOrIncl(s)
template emitData(t: Token) = c.data.add t
template emitData(t: PredefinedToken) = c.data.add Token(t)

proc genStrLit(c: var GeneratedCode; litId: StrId): Token =
  let cstr = makeCString(c.m.lits.strings[litId])
  result = c.tokens.getOrIncl cstr

type
  ProcFlag = enum
    isSelectAny, isVarargs, isInline

proc genProcPragmas(g: var GeneratedCode; t: Tree; n: NodePos;
                    flags: var set[ProcFlag]) =
  # ProcPragma ::= (inline) | (noinline) | CallingConvention | (varargs) | (was Identifier) |
  #               (selectany) | Attribute
  if t[n].kind == Empty:
    discard
  elif t[n].kind == PragmasC:
    for ch in sons(t, n):
      case t[ch].kind
      of CallingConventions:
        g.add " __" & $t[ch].kind
      of VarargsC:
        flags.incl isVarargs
      of SelectanyC:
        flags.incl isSelectAny
      of InlineC:
        flags.incl isInline
      of AttrC:
        g.add " __attribute__((" & toString(t, ch.firstSon, g.m) & "))"
      of NoinlineC:
        g.add " __attribute__((noinline))"
      of WasC:
        g.add "/* " & toString(t, ch.firstSon, g.m) & " */"
      else:
        error g.m, "invalid proc pragma: ", t, ch
  else:
    error g.m, "expected proc pragmas but got: ", t, n

proc genSymDef(g: var GeneratedCode; t: Tree; n: NodePos): string =
  if t[n].kind == SymDef:
    let lit = t[n].litId
    result = mangle(g.m.lits.strings[lit])
    g.add result
  else:
    error g.m, "expected SymbolDef but got: ", t, n
    result = ""

proc genParamPragmas(g: var GeneratedCode; t: Tree; n: NodePos) =
  # ProcPragma ::= (was Identifier) | Attribute
  if t[n].kind == Empty:
    discard
  elif t[n].kind == PragmasC:
    for ch in sons(t, n):
      case t[ch].kind
      of AttrC:
        g.add " __attribute__((" & toString(t, ch.firstSon, g.m) & "))"
      of WasC:
        g.add "/* " & toString(t, ch.firstSon, g.m) & " */"
      else:
        error g.m, "invalid pragma: ", t, ch
  else:
    error g.m, "expected pragmas but got: ", t, n

proc genParam(g: var GeneratedCode; t: Tree; n: NodePos) =
  let d = asParamDecl(t, n)
  if t[d.name].kind == SymDef:
    let lit = t[d.name].litId
    let name = mangle(g.m.lits.strings[lit])
    genType g, t, d.typ, name
    genParamPragmas g, t, d.pragmas
  else:
    error g.m, "expected SymbolDef but got: ", t, n

proc genVarPragmas(g: var GeneratedCode; t: Tree; n: NodePos) =
  if t[n].kind == Empty:
    discard
  elif t[n].kind == PragmasC:
    for ch in sons(t, n):
      case t[ch].kind
      of TlsC:
        g.add " __thread"
      of AlignC:
        g.add " NIM_ALIGN(" & toString(t, ch.firstSon, g.m) & ")"
      of AttrC:
        g.add " __attribute__((" & toString(t, ch.firstSon, g.m) & "))"
      of WasC:
        g.add "/* " & toString(t, ch.firstSon, g.m) & " */"
      else:
        error g.m, "invalid pragma: ", t, ch
  else:
    error g.m, "expected pragmas but got: ", t, n

include genexprs

proc genVarDecl(g: var GeneratedCode; t: Tree; n: NodePos; prefix: PredefinedToken) =
  let d = asVarDecl(t, n)
  if t[d.name].kind == SymDef:
    let lit = t[d.name].litId
    let name = mangle(g.m.lits.strings[lit])
    g.add prefix
    genType g, t, d.typ, name
    genVarPragmas g, t, d.pragmas
    if t[d.value].kind != Empty:
      g.add AsgnOpr
      genx g, t, d.value
    g.add Semicolon
  else:
    error g.m, "expected SymbolDef but got: ", t, n

template moveToDataSection(body: untyped) =
  let oldLen = c.code.len
  body
  for i in oldLen ..< c.code.len:
    c.data.add c.code[i]
  setLen c.code, oldLen

include genstmts

proc genProcDecl(g: var GeneratedCode; t: Tree; n: NodePos; isExtern: bool) =
  let signatureBegin = g.code.len
  let prc = asProcDecl(t, n)

  if isExtern:
    g.add ExternKeyword

  genType g, t, prc.returnType
  g.add Space
  let name = genSymDef(g, t, prc.name)

  var flags: set[ProcFlag] = {}
  genProcPragmas g, t, prc.pragmas, flags

  g.add ParLe

  var params = 0
  for ch in sons(t, prc.params):
    if params > 0: g.add Comma
    genParam g, t, ch
    inc params

  if isVarargs in flags:
    if params > 0: g.add Comma
    g.add "..."
    inc params

  if params == 0:
    g.add "void"
  g.add ParRi

  if isExtern or g.requestedSyms.contains(name):
    # symbol was used before its declaration has been processed so
    # add a signature:
    for i in signatureBegin ..< g.code.len:
      g.protos.add g.code[i]
    g.protos.add Token Semicolon

  if isExtern:
    g.code.setLen signatureBegin
  else:
    g.add CurlyLe
    genStmt g, t, prc.body
    g.add CurlyRi

proc genInclude(c: var GeneratedCode; t: Tree; n: NodePos) =
  let lit = t[n.firstSon].litId
  let headerAsStr {.cursor.} = c.m.lits.strings[lit]
  let header = c.tokens.getOrIncl(headerAsStr)
  if headerAsStr.len > 0 and not c.includedHeaders.containsOrIncl(int header):
    if headerAsStr[0] == '#':
      discard "skip the #include keyword"
    else:
      c.includes.add Token(IncludeKeyword)
    c.includes.add header
    c.includes.add Token NewLine

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
  of ImpC: genImp(c, t, n)
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

  when false:
    var i = NodePos(0)
    while i.int < c.m.code.len:
      let oldLen = c.code.len
      let moveToInitSection = false # c.m.code[NodePos(i)].kind notin AllowedInToplevelC

      gen c, c.m.code, NodePos(i)
      next c.m.code, i

      if moveToInitSection:
        for i in oldLen ..< c.code.len:
          c.init.add c.code[i]
        setLen c.code, oldLen

proc generateCode*(inp, outp: string; intmSize: int) =
  var c = initGeneratedCode(load(inp))

  var co = TypeOrder()
  traverseTypes(c.m, co)

  generateTypes(c, c.m.types, co)
  let typeDecls = move c.code

  traverseCode c, c.m.code, StartPos
  var f = CppFile(f: open(outp, fmWrite))
  f.write "#define NIM_INTBITS " & $intmSize & "\n"
  f.write Prelude
  writeTokenSeq f, c.includes, c
  writeTokenSeq f, typeDecls, c
  writeTokenSeq f, c.data, c
  writeTokenSeq f, c.protos, c
  writeTokenSeq f, c.code, c
  if c.init.len > 0:
    f.write "void __attribute__((constructor)) init(void) {"
    writeTokenSeq f, c.init, c
    f.write "}\n\n"
  f.f.close

  if c.headerFile.len > 0:
    var h = open(outp.changeFileExt(".h"), fmWrite)
    for x in items(c.headerFile):
      write h, c.tokens[x]
    h.close()
