#
#
#           NIFC Compiler
#        (c) Copyright 2024 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# included from genpreasm.nim

proc genx(c: var GeneratedCode; t: Tree; n: NodePos)

template typedBinOp(opr) =
  let (typ, a, b) = sons3(t, n)
  c.add ParLe
  c.add ParLe
  genType c, t, typ
  c.add ParRi
  genx c, t, a
  c.add opr
  genx c, t, b
  c.add ParRi

template cmpOp(opr) =
  let (a, b) = sons2(t, n)
  c.add ParLe
  genx c, t, a
  c.add opr
  genx c, t, b
  c.add ParRi

template unOp(opr) =
  c.add ParLe
  c.add opr
  genx c, t, n.firstSon
  c.add ParRi

template typedUnOp(opr) =
  let (typ, a) = sons2(t, n)
  c.add ParLe
  c.add ParLe
  genType c, t, typ
  c.add ParRi
  c.add opr
  genx c, t, a
  c.add ParRi

proc genCall(c: var GeneratedCode; t: Tree; n: NodePos) =
  c.buildTree CallT, t[n].info:
    for ch in sons(t, n):
      genx c, t, ch

proc genLvalue(c: var GeneratedCode; t: Tree; n: NodePos) =
  case t[n].kind
  of Sym:
    let lit = t[n].litId
    let name = mangle(c.m.lits.strings[lit])
    c.add name
    c.requestedSyms.incl name
  of DerefC: unOp "*"
  of AtC:
    let (a, i) = sons2(t, n)
    genx c, t, a
    c.add Dot
    c.add "a"
    c.add BracketLe
    genx c, t, i
    c.add BracketRi
  of PatC:
    let (a, i) = sons2(t, n)
    genx c, t, a
    c.add BracketLe
    genx c, t, i
    c.add BracketRi
  of DotC:
    let (obj, fld, inheritance) = sons3(t, n)
    let inhs {.cursor.} = c.m.lits.strings[t[inheritance].litId]
    if inhs != "0":
      var inh = parseInt(inhs)
      genx c, t, obj
      while inh > 0:
        c.add ".Q"
        dec inh
    c.add Dot
    genx c, t, fld
  else:
    error c.m, "expected expression but got: ", t, n

proc objConstrType(c: var GeneratedCode; t: Tree; n: NodePos) =
  # C99 is strange, it requires (T){} for struct construction but not for
  # consts.
  if c.inSimpleInit == 0:
    c.add ParLe
    genType(c, t, n)
    c.add ParRi

proc genx(c: var GeneratedCode; t: Tree; n: NodePos) =
  case t[n].kind
  of IntLit:
    genIntLit c, t[n].litId
  of UIntLit:
    genUIntLit c, t[n].litId
  of FloatLit:
    c.add c.m.lits.strings[t[n].litId]
  of CharLit:
    let ch = t[n].uoperand
    var s = "'"
    toCChar char(ch), s
    s.add "'"
    c.add s
  of FalseC: c.add "NIM_FALSE"
  of TrueC: c.add "NIM_TRUE"
  of StrLit:
    c.add makeCString(c.m.lits.strings[t[n].litId])
  of NilC:
    c.add NullPtr
  of AconstrC:
    c.objConstrType(t, n.firstSon)
    c.add CurlyLe
    c.add ".a = "
    c.add CurlyLe
    var i = 0
    for ch in sonsFromX(t, n):
      if i > 0: c.add Comma
      c.genx t, ch
      inc i
    c.add CurlyRi
    c.add CurlyRi
  of OconstrC:
    c.objConstrType(t, n.firstSon)
    c.add CurlyLe
    var i = 0
    for ch in sonsFromX(t, n):
      if i > 0: c.add Comma
      if t[ch].kind == OconstrC:
        # inheritance
        c.add Dot
        c.add "Q"
        c.add AsgnOpr
        c.genx t, ch
      else:
        let (k, v) = sons2(t, ch)
        c.add Dot
        c.genx t, k
        c.add AsgnOpr
        c.genx t, v
      inc i
    c.add CurlyRi
  of ParC:
    let arg = n.firstSon
    c.add ParLe
    genx c, t, arg
    c.add ParRi
  of AddrC: unOp "&"
  of SizeofC:
    let arg = n.firstSon
    c.add "sizeof"
    c.add ParLe
    genx c, t, arg
    c.add ParRi
  of CallC: genCall c, t, n
  of AddC: typedBinOp " + "
  of SubC: typedBinOp " - "
  of MulC: typedBinOp " * "
  of DivC: typedBinOp " / "
  of ModC: typedBinOp " % "
  of ShlC: typedBinOp " << "
  of ShrC: typedBinOp " >> "
  of BitandC: typedBinOp " & "
  of BitorC: typedBinOp " | "
  of BitxorC: typedBinOp " ^ "
  of BitnotC: typedUnOp " ~ "
  of AndC: cmpOp " && "
  of OrC: cmpOp " || "
  of NotC: cmpOp " !"
  of NegC: cmpOp " -"
  of EqC: cmpOp " == "
  of LeC: cmpOp " <= "
  of LtC: cmpOp " < "
  of CastC: typedUnOp ""
  of ConvC: typedUnOp ""
  of SufC:
    let (value, suffix) = sons2(t, n)
    genx(c, t, value)
  else:
    genLvalue c, t, n
