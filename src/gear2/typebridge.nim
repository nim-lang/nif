#       Nifler
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

# included from bridge.nim

## Implements the mapping from Nim type graph to NIF ("gear2").

proc isNominalRef(t: PType): bool {.inline.} =
  let e = t.elementType
  t.sym != nil and e.kind == tyObject and (e.sym == nil or sfAnon in e.sym.flags)

template singleElement(keyw: string) {.dirty.} =
  c.b.withTree keyw:
    if t.hasElementType:
      toNif t.elementType, parent, c
    else:
      c.b.addEmpty

proc toNif*(t: PType; parent: PNode; c: var WContext) =
  case t.kind
  of tyNone: c.b.addKeyw typeKindToTag(t.kind)
  of tyBool: c.b.addKeyw typeKindToTag(t.kind)
  of tyChar: c.b.addKeyw "c 8"
  of tyEmpty: c.b.addEmpty
  of tyInt: c.b.addKeyw "i M"
  of tyInt8: c.b.addKeyw "i 8"
  of tyInt16: c.b.addKeyw "i 16"
  of tyInt32: c.b.addKeyw "i 32"
  of tyInt64: c.b.addKeyw "i 64"
  of tyUInt: c.b.addKeyw "u M"
  of tyUInt8: c.b.addKeyw "u 8"
  of tyUInt16: c.b.addKeyw "u 16"
  of tyUInt32: c.b.addKeyw "u 32"
  of tyUInt64: c.b.addKeyw "u 64"
  of tyFloat, tyFloat64: c.b.addKeyw "f 64"
  of tyFloat32: c.b.addKeyw "f 32"
  of tyFloat128: c.b.addKeyw "f 128"
  of tyAlias:
    # XXX Generic aliases are no aliases
    toNif t.skipModifier, parent, c
  of tyNil: c.b.addKeyw typeKindToTag(t.kind)
  of tyUntyped: c.b.addKeyw typeKindToTag(t.kind)
  of tyTyped: c.b.addKeyw typeKindToTag(t.kind)
  of tyTypeDesc:
    c.b.withTree typeKindToTag(t.kind):
      if t.kidsLen == 0 or t.elementType.kind == tyNone:
        c.b.addEmpty
      else:
        toNif t.elementType, parent, c
  of tyGenericParam:
    # See the nim-sem spec:
    c.b.withTree typeKindToTag(t.kind):
      symToNif t.sym, c
      c.b.addIntLit t.sym.position

  of tyGenericInst:
    c.b.withTree typeKindToTag(t.kind):
      toNif t.genericHead, parent, c
      for _, a in t.genericInstParams:
        toNif a, parent, c
  of tyGenericInvocation:
    c.b.withTree typeKindToTag(t.kind):
      toNif t.genericHead, parent, c
      for _, a in t.genericInvocationParams:
        toNif a, parent, c
  of tyGenericBody:
    toNif t.last, parent, c
    # Alternatively something with `genericBodyParams`...
  of tyDistinct, tyEnum:
    symToNif t.sym, c
  of tyPtr:
    if isNominalRef(t):
      symToNif t.sym, c
    else:
      c.b.withTree typeKindToTag(t.kind):
        toNif t.elementType, parent, c
  of tyRef:
    if isNominalRef(t):
      symToNif t.sym, c
    else:
      c.b.withTree typeKindToTag(t.kind):
        toNif t.elementType, parent, c
  of tyVar:
    c.b.withTree(if isOutParam(t): "out" else: "mut"):
      toNif t.elementType, parent, c
  of tyAnd:
    c.b.withTree typeKindToTag(t.kind):
      for _, son in t.ikids: toNif son, parent, c
  of tyOr:
    c.b.withTree typeKindToTag(t.kind):
      for _, son in t.ikids: toNif son, parent, c
  of tyNot:
    c.b.withTree typeKindToTag(t.kind): toNif t.elementType, parent, c

  of tyFromExpr:
    if t.n == nil:
      c.b.addKeyw "err"
    else:
      c.b.withTree typeKindToTag(t.kind):
        toNif t.n, parent, c

  of tyArray:
    c.b.withTree typeKindToTag(t.kind):
      if t.hasElementType:
        toNif t.elementType, parent, c
        toNif t.indexType, parent, c
      else:
        c.b.addEmpty 2
  of tyUncheckedArray:
    c.b.withTree typeKindToTag(t.kind):
      if t.hasElementType:
        toNif t.elementType, parent, c
      else:
        c.b.addEmpty

  of tySequence:
    singleElement typeKindToTag(t.kind)

  of tyOrdinal:
    c.b.withTree typeKindToTag(t.kind):
      if t.hasElementType:
        toNif t.skipModifier, parent, c
      else:
        c.b.addEmpty

  of tySet: singleElement typeKindToTag(t.kind)
  of tyOpenArray: singleElement typeKindToTag(t.kind)
  of tyIterable: singleElement typeKindToTag(t.kind)
  of tyLent: singleElement typeKindToTag(t.kind)

  of tyTuple:
    c.b.withTree typeKindToTag(t.kind):
      if t.n != nil:
        for i in 0..<t.n.len:
          assert(t.n[i].kind == nkSym)
          c.b.withTree "kv":
            c.b.addIdent t.n[i].sym.name.s
            toNif t.n[i].sym.typ, parent, c
      else:
        for _, son in t.ikids: toNif son, parent, c

  of tyRange:
    c.b.withTree typeKindToTag(t.kind):
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
          c.b.addKeyw ($t.callConv).toLowerAscii.substr(2)

  of tyVarargs:
    c.b.withTree typeKindToTag(t.kind):
      if t.hasElementType:
        toNif t.elementType, parent, c
      else:
        c.b.addEmpty
      if t.n != nil:
        toNif t.n, parent, c
      else:
        c.b.addEmpty

  of tySink: singleElement typeKindToTag(t.kind)
  of tyOwned: singleElement typeKindToTag(t.kind)
  of tyVoid: c.b.addKeyw typeKindToTag(t.kind)
  of tyPointer: c.b.addKeyw typeKindToTag(t.kind)
  of tyString: c.b.addKeyw typeKindToTag(t.kind)
  of tyCstring: c.b.addKeyw typeKindToTag(t.kind)
  of tyObject: symToNif t.sym, c
  of tyForward: c.b.addKeyw typeKindToTag(t.kind)
  of tyProxy: c.b.addKeyw typeKindToTag(t.kind)
  of tyBuiltInTypeClass:
    # XXX See what to do with this.
    c.b.withTree typeKindToTag(t.kind):
      if t.kidsLen == 0 or t.genericHead.kind == tyNone:
        c.b.addEmpty
      else:
        toNif t.genericHead, parent, c

  of tyUserTypeClass, tyConcept:
    # ^ old style concept.  ^ new style concept.
    if t.sym != nil:
      symToNif t.sym, c
    else:
      c.b.addKeyw "err"
  of tyUserTypeClassInst:
    # "instantiated" old style concept. Whatever that even means.
    if t.sym != nil:
      symToNif t.sym, c
    else:
      c.b.addKeyw "err"
  of tyCompositeTypeClass: toNif t.last, parent, c
  of tyInferred: toNif t.skipModifier, parent, c
  of tyAnything: c.b.addKeyw typeKindToTag(t.kind)
  of tyStatic:
    c.b.withTree typeKindToTag(t.kind):
      if t.hasElementType:
        toNif t.skipModifier, parent, c
      else:
        c.b.addEmpty
      if t.n != nil:
        toNif t.n, parent, c
      else:
        c.b.addEmpty
