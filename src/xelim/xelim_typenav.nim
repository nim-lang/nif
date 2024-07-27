#       Nif library
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## A type navigator can recompute the type of an expression.

import std / tables
import "../lib" / [bitabs, packedtrees]

import xelim_model

type
  TypeDesc* {.acyclic.} = object
    p: NodePos
    a: Node
    down, next: ref TypeDesc
  TypeDescRef = ref TypeDesc

proc errorType(): TypeDesc = TypeDesc(p: NodePos(0), a: createAtom(AutoX))

proc createIntegralType(lits: var Literals; integral, bits: string): TypeDesc =
  result = TypeDesc(p: NodePos(0), a: createAtom(Other),
    down: TypeDescRef(p: NodePos(0), a: createAtom(Tag, lits.tags.getOrIncl(integral))))
  result.down.next = TypeDescRef(p: NodePos(0), a: createAtom(IntLit, lits.strings.getOrIncl(bits)))

proc atomType(lits: var Literals; name: string): TypeDesc =
  result = TypeDesc(p: NodePos(0), a: createAtom(Other),
    down: TypeDescRef(p: NodePos(0), a: createAtom(Tag, lits.tags.getOrIncl(name))))

proc extractSuffix(s: string): string =
  var i = s.len-1
  while i > 0 and s[i] in {'0'..'9'}: dec i
  if i != s.len-1 and i > 0 and s[i] in {'A'..'Z', 'a'..'z'}:
    result = substr(s, i+1)
  else:
    result = "M"

proc integralType(m: var Module; t: Tree; n: NodePos; integral: string): TypeDesc =
  let bits = extractSuffix(m.lits.strings[t[n].litId])
  result = createIntegralType(m.lits, integral, bits)

proc copyType*(dest: var Tree; t: Tree; typ: TypeDesc) =
  if typ.p != NodePos(0):
    copyTree dest, t, typ.p
  else:
    if isAtom(typ.a.kind):
      dest.copyNode typ.a
    else:
      copyInto dest, typ.a.kind, typ.a.info:
        var it {.cursor.} = typ.down
        while it != nil:
          copyType(dest, t, it[])
          it = it.next

proc elemType(t: Tree; typ: TypeDesc): TypeDesc =
  if typ.p != NodePos(0):
    result = TypeDesc(p: ithSon(t, typ.p, 1))
  else:
    result = typ.down[]

proc makePtrType(m: var Module; typ: TypeDesc): TypeDesc =
  result = atomType(m.lits, "ptr")
  result.down.next = TypeDescRef(p: typ.p, a: typ.a, down: typ.down)

proc getType*(m: var Module; t: Tree; n: NodePos): TypeDesc =
  case t[n].kind
  of Empty, Ident, Symdef, BoolX, AutoX, Err:
    result = errorType()
  of Sym:
    let d = m.defs.getOrDefault(t[n].litId)
    if d != NodePos(0):
      result = getType(m, t, d)
    else:
      result = errorType()
  of LetX, VarX, CursorX, ConstX: #, ParamX:
    let i = ithSon(t, n, 3)
    result = TypeDesc(p: i)
  of IntLit: result = integralType(m, t, n, "i")
  of UIntLit: result = integralType(m, t, n, "u")
  of FloatLit: result = integralType(m, t, n, "f")
  of CharLit: result = createIntegralType(m.lits, "c", "8")
  of StrLit: result = atomType(m.lits, "str")
  of TrueX, FalseX, AndX, OrX: result = atomType(m.lits, "bool")
  of IfX, ElseX, TryX, TypeofX:
    result = getType(m, t, n.firstSon)
  of CaseX, ExprX, ElifX, OfX, ExceptX:
    result = getType(m, t, ithSon(t, n, 1))
  of CallX:
    let procType = getType(m, t, n.firstSon)
    if procType.p != NodePos(0):
      assert t[procType.p].kind == ProcX
      result = TypeDesc(p: ithSon(t, n, ReturnTypePos))
    else:
      result = procType # propagate error
  of Other:
    case m.lits.tags[t[n.firstSon].tagId]
    of "at":
      let (_, arr, _) = sons3(t, n)
      let arrayType = getType(m, t, arr)
      result = elemType(t, arrayType)
    of "dot":
      let (_, _, field) = sons3(t, n)
      result = getType(m, t, field)
    of "deref", "hderef":
      let (_, ex) = sons2(t, n)
      let ptrType = getType(m, t, ex)
      result = elemType(t, ptrType)
    of "addr", "haddr":
      let (_, ex) = sons2(t, n)
      let varType = getType(m, t, ex)
      result = makePtrType(m, varType)
    of "hconv", "conv", "cast", "oconstr", "aconstr", "sconstr", "tupleconstr":
      result = TypeDesc(p: ithSon(t, n, 1))
    of "blockexpr":
      result = TypeDesc(p: ithSon(t, n, 2))
    else:
      result = errorType()
  of Tag, AsgnX, RetX, DiscardX, RaiseX, YieldX, BreakX, WhileX, FinallyX, ProcX, StmtsX:
    result = errorType()
