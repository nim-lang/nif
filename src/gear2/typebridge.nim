#       Nifler
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

# included from bridge.nim

## Implements the mapping from Nim type graph to NIF ("gear2").

proc writeFlags[E](b: var Builder; flags: set[E]; tag: string) =
  var flagsAsIdent = ""
  genFlags(flags, flagsAsIdent)
  if flagsAsIdent.len > 0:
    b.withTree tag:
      b.addIdent flagsAsIdent

proc writeTypeFlags(c: var WContext; t: PType) =
  writeFlags c.b, t.flags, "tf"

proc isNominalRef(t: PType): bool {.inline.} =
  let e = t.elementType
  t.sym != nil and e.kind == tyObject and (e.sym == nil or sfAnon in e.sym.flags)

template singleElement(keyw: string) {.dirty.} =
  c.b.withTree keyw:
    writeTypeFlags(c, t)
    if t.hasElementType:
      toNif t.elementType, parent, c
    else:
      c.b.addEmpty

proc atom(t: PType; c: var WContext; tag: string) =
  c.b.withTree tag:
    writeTypeFlags(c, t)

proc atom(t: PType; c: var WContext) =
  c.b.withTree toNifTag(t.kind):
    writeTypeFlags(c, t)

template typeHead(c: var WContext; t: PType; body: untyped) =
  c.b.withTree toNifTag(t.kind):
    writeTypeFlags(c, t)
    body

proc toNif*(t: PType; parent: PNode; c: var WContext) =
  if t == nil:
    c.b.addKeyw "missing"
    return

  case t.kind
  of tyNone: atom t, c
  of tyBool: atom t, c
  of tyChar: atom t, c, "c 8"
  of tyEmpty: c.b.addEmpty
  of tyInt: atom t, c, "i -1"
  of tyInt8: atom t, c, "i 8"
  of tyInt16: atom t, c, "i 16"
  of tyInt32: atom t, c, "i 32"
  of tyInt64: atom t, c, "i 64"
  of tyUInt: atom t, c, "u -1"
  of tyUInt8: atom t, c, "u 8"
  of tyUInt16: atom t, c, "u 16"
  of tyUInt32: atom t, c, "u 32"
  of tyUInt64: atom t, c, "u 64"
  of tyFloat, tyFloat64: atom t, c, "f 64"
  of tyFloat32: atom t, c, "f 32"
  of tyFloat128: atom t, c, "f 128"
  of tyAlias:
    c.typeHead t:
      toNif t.skipModifier, parent, c
  of tyNil: atom t, c
  of tyUntyped: atom t, c
  of tyTyped: atom t, c
  of tyTypeDesc:
    c.typeHead t:
      if t.kidsLen == 0 or t.elementType.kind == tyNone:
        c.b.addEmpty
      else:
        toNif t.elementType, parent, c
  of tyGenericParam:
    # See the nim-sem spec:
    c.typeHead t:
      symToNif t.sym, c
      #c.b.addIntLit t.sym.position

  of tyGenericInst:
    c.typeHead t:
      toNif t.genericHead, parent, c
      for _, a in t.genericInstParams:
        toNif a, parent, c
  of tyGenericInvocation:
    c.typeHead t:
      toNif t.genericHead, parent, c
      for _, a in t.genericInvocationParams:
        toNif a, parent, c
  of tyGenericBody:
    #toNif t.last, parent, c
    c.typeHead t:
      for _, son in t.ikids: toNif son, parent, c
  of tyDistinct, tyEnum:
    if t.sym != nil:
      symToNif t.sym, c
    else:
      c.typeHead t:
        for _, son in t.ikids: toNif son, parent, c
  of tyPtr:
    if isNominalRef(t):
      symToNif t.sym, c
    else:
      c.typeHead t:
        toNif t.elementType, parent, c
  of tyRef:
    if isNominalRef(t):
      symToNif t.sym, c
    else:
      c.typeHead t:
        toNif t.elementType, parent, c
  of tyVar:
    c.b.withTree(if isOutParam(t): "out" else: "mut"):
      toNif t.elementType, parent, c
  of tyAnd:
    c.typeHead t:
      for _, son in t.ikids: toNif son, parent, c
  of tyOr:
    c.typeHead t:
      for _, son in t.ikids: toNif son, parent, c
  of tyNot:
    c.typeHead t: toNif t.elementType, parent, c

  of tyFromExpr:
    if t.n == nil:
      atom t, c, "err"
    else:
      c.typeHead t:
        toNif t.n, parent, c

  of tyArray:
    c.typeHead t:
      if t.hasElementType:
        toNif t.elementType, parent, c
        toNif t.indexType, parent, c
      else:
        c.b.addEmpty 2
  of tyUncheckedArray:
    c.typeHead t:
      if t.hasElementType:
        toNif t.elementType, parent, c
      else:
        c.b.addEmpty

  of tySequence:
    singleElement toNifTag(t.kind)

  of tyOrdinal:
    c.typeHead t:
      if t.hasElementType:
        toNif t.skipModifier, parent, c
      else:
        c.b.addEmpty

  of tySet: singleElement toNifTag(t.kind)
  of tyOpenArray: singleElement toNifTag(t.kind)
  of tyIterable: singleElement toNifTag(t.kind)
  of tyLent: singleElement toNifTag(t.kind)

  of tyTuple:
    c.typeHead t:
      if t.n != nil:
        for i in 0..<t.n.len:
          assert(t.n[i].kind == nkSym)
          c.b.withTree "kv":
            c.b.addIdent t.n[i].sym.name.s
            toNif t.n[i].sym.typ, parent, c
      else:
        for _, son in t.ikids: toNif son, parent, c

  of tyRange:
    c.typeHead t:
      toNif t.elementType, parent, c
      if t.n != nil and t.n.kind == nkRange and t.n.len == 2:
        toNif t.n[0], parent, c
        toNif t.n[1], parent, c
      else:
        c.b.addEmpty 2

  of tyProc:
    let kind = if tfIterator in t.flags: "iteratortype"
               else: "proctype"
    c.b.withTree kind:

      c.b.addEmpty # name
      for i, a in t.paramTypes:
        let j = paramTypeToNodeIndex(i)
        if t.n != nil and j < t.n.len and t.n[j].kind == nkSym:
          c.b.addIdent(t.n[j].sym.name.s)
          toNif a, parent, c
      if tfUnresolved in t.flags:
        c.b.addRaw "[*missing parameters*]"
      if t.returnType != nil:
        toNif t.returnType, parent, c
      else:
        c.b.addEmpty

      c.b.withTree "effects":
        # XXX model explicit .raises and .tags annotations
        if tfNoSideEffect in t.flags:
          c.b.addKeyw "noside"
        if tfThread in t.flags:
          c.b.addKeyw "gcsafe"

      c.b.withTree "pragmas":
        if t.callConv == ccNimCall and tfExplicitCallConv notin t.flags:
          discard "no calling convention to generate"
        else:
          c.b.addKeyw toNifTag(t.callConv)

  of tyVarargs:
    c.typeHead t:
      if t.hasElementType:
        toNif t.elementType, parent, c
      else:
        c.b.addEmpty
      if t.n != nil:
        toNif t.n, parent, c
      else:
        c.b.addEmpty

  of tySink: singleElement toNifTag(t.kind)
  of tyOwned: singleElement toNifTag(t.kind)
  of tyVoid: atom t, c
  of tyPointer: atom t, c
  of tyString: atom t, c
  of tyCstring: atom t, c
  of tyObject: symToNif t.sym, c
  of tyForward: atom t, c
  of tyError: atom t, c
  of tyBuiltInTypeClass:
    # XXX See what to do with this.
    c.typeHead t:
      if t.kidsLen == 0 or t.genericHead.kind == tyNone:
        c.b.addEmpty
      else:
        toNif t.genericHead, parent, c

  of tyUserTypeClass, tyConcept:
    # ^ old style concept.  ^ new style concept.
    if t.sym != nil:
      symToNif t.sym, c
    else:
      atom t, c, "err"
  of tyUserTypeClassInst:
    # "instantiated" old style concept. Whatever that even means.
    if t.sym != nil:
      symToNif t.sym, c
    else:
      atom t, c, "err"
  of tyCompositeTypeClass: toNif t.last, parent, c
  of tyInferred: toNif t.skipModifier, parent, c
  of tyAnything: atom t, c
  of tyStatic:
    c.typeHead t:
      if t.hasElementType:
        toNif t.skipModifier, parent, c
      else:
        c.b.addEmpty
      if t.n != nil:
        toNif t.n, parent, c
      else:
        c.b.addEmpty
