#       Nimony
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

import std / [sets, tables]

import bitabs, nifreader, nifstreams, nifcursors, lineinfos

import ".." / specs / tags
import programs, decls

proc addStrLit*(dest: var TokenBuf; s: string; info = NoLineInfo) =
  dest.add toToken(StringLit, pool.strings.getOrIncl(s), info)

proc addIntLit*(dest: var TokenBuf; i: BiggestInt; info = NoLineInfo) =
  dest.add toToken(IntLit, pool.integers.getOrIncl(i), info)

type
  TypeModifier* = enum
    NoneM, MutM, OutM, LentM, SinkM, StaticM

type
  Match* = object
    inferred: Table[SymId, Cursor]
    tvars: HashSet[SymId]
    args*, typeArgs*: TokenBuf
    err*: bool
    skippedMod: TypeModifier
    argInfo: PackedLineInfo
    pos, opened: int
    inheritanceCosts, intCosts: int

proc createMatch*(): Match = Match()

proc error(m: var Match; msg: string) =
  if m.err: return # first error is the important one
  m.args.addParLe ErrT, m.argInfo
  m.args.addStrLit "[" & $m.pos & "] " # at position [x]
  m.args.addStrLit msg
  m.args.addParRi()
  m.err = true

proc concat(a: varargs[string]): string =
  result = a[0]
  for i in 1..high(a): result.add a[i]

proc expected(f, a: Cursor): string =
  concat("expected: ", toString(f), " but got: ", toString(a))

proc typeImpl(s: SymId): Cursor =
  let buf = loadSym(s)
  result = beginRead(buf[])
  assert result.tag == TypeT
  inc result # skip ParLe
  for i in 1..4:
    skip(result) # name, export marker, pragmas, generic parameter

proc objtypeImpl(s: SymId): Cursor =
  result = typeImpl(s)
  if result.tag == RefT or result.tag == PtrT:
    inc result

proc isObjectType(s: SymId): bool =
  let impl = objtypeImpl(s)
  result = impl.tag == ObjectT

proc isConcept(s: SymId): bool =
  #let impl = typeImpl(s)
  # XXX Model Concept in the grammar
  #result = impl.tag == ConceptT
  result = false

proc asTypeAlias(s: SymId): Cursor =
  let impl = typeImpl(s)
  if impl.kind == Symbol or impl.tag == InvokT:
    result = impl
  else:
    result = errCursor()

iterator inheritanceChain(s: SymId): SymId =
  var objbody = objtypeImpl(s)
  while true:
    let od = asObjectDecl(objbody)
    if od.tag == ObjectT:
      var parent = od.parentType
      if parent.tag == RefT or parent.tag == PtrT:
        inc parent
      if parent.kind == Symbol:
        let ps = parent.symId
        yield ps
        objbody = objtypeImpl(ps)
      else:
        break
    else:
      break

proc matchesConstraint(m: var Match; f: var Cursor; a: Cursor): bool =
  result = false
  if f.kind == DotToken:
    result = true
  elif a.kind == Symbol:
    result = matchesConstraint(m, f, typeImpl(a.symId))
  elif f.kind == ParLe:
    if f.tagId == OrT:
      inc f
      while f.kind != ParRi:
        if matchesConstraint(m, f, a):
          result = true
          break
      if f.kind == ParRi: inc f
    elif a.kind == ParLe:
      result = f.tagId == a.tagId
      inc f
      if f.kind == ParRi: inc f

proc matchesConstraint(m: var Match; f: SymId; a: Cursor): bool =
  var f = typeImpl(f)
  result = matchesConstraint(m, f, a)

proc linearMatch(m: var Match; f, a: var Cursor) =
  var nested = 0
  while true:
    if f.kind == Symbol and m.tvars.contains(f.symId):
      # type vars are specal:
      let fs = f.symId
      if m.inferred.contains(fs):
        # rematch?
        linearMatch(m, m.inferred[fs], a)
        if m.err: break
      elif matchesConstraint(m, fs, a):
        m.inferred[fs] = a # NOTICE: Can introduce modifiers for a type var!
      else:
        m.error concat(toString(a), " does not match constraint ", toString(f))
        break
    elif f.kind == a.kind:
      case f.kind
      of UnknownToken, EofToken,
          DotToken, Ident, Symbol, SymbolDef,
          StringLit, CharLit, IntLit, UIntLit, FloatLit:
        if f.uoperand != a.uoperand:
          m.error expected(f, a)
          break
      of ParLe:
        if f.uoperand != a.uoperand:
          m.error expected(f, a)
          break
        inc nested
      of ParRi:
        if nested == 0: break
        dec nested
    else:
      m.error expected(f, a)
      break
    inc f
    inc a

proc modtag(c: Cursor): TypeModifier =
  let t = c.tag
  if t == MutT: MutM
  elif t == OutT: OutM
  elif t == LentT: LentM
  elif t == SinkT: SinkM
  elif t == StatT: StaticM
  else: NoneM

proc skipModifier(a: Cursor): Cursor =
  result = a
  if result.kind == ParLe and result.modtag != NoneM:
    inc result

proc commonType(f, a: Cursor): Cursor =
  # XXX Refine
  result = a

proc typevarRematch(m: var Match; typeVar: SymId; f, a: Cursor) =
  let com = commonType(f, a)
  if com.kind == ParLe and com.tagId == ErrT:
    m.error concat("could not match again: ", pool.syms[typeVar], "; expected ",
      toString(f), " but got ", toString(a))
  elif matchesConstraint(m, typeVar, com):
    m.inferred[typeVar] = skipModifier(com)
  else:
    m.error concat(toString(a), " does not match constraint ", toString(typeImpl typeVar))

type
  ArgItem* = object
    n*, typ*: Cursor

proc useArg(m: var Match; arg: ArgItem) =
  var usedDeref = false
  if arg.typ.modtag in {MutM, LentM, OutM} and m.skippedMod notin {MutM, LentM, OutM}:
    m.args.addParLe HderefT, arg.n.info
    usedDeref = true
  m.args.addSubtree arg.n
  if usedDeref:
    m.args.addParRi()

proc singleArg(m: var Match; f: var Cursor; arg: ArgItem)

proc matchSymbol(m: var Match; f: Cursor; arg: ArgItem) =
  let a = skipModifier(arg.typ)
  let fs = f.symId
  if m.tvars.contains(fs):
    # it is a type var we own
    if m.inferred.contains(fs):
      typevarRematch(m, fs, m.inferred[fs], a)
    elif matchesConstraint(m, fs, a):
      m.inferred[fs] = a
    else:
      m.error concat(toString(a), " does not match constraint ", toString(f))
  elif isObjectType(fs):
    if a.kind != Symbol:
      m.error expected(f, a)
    elif a.symId == fs:
      discard "direct match, no annotation required"
    else:
      var diff = 1
      for fparent in inheritanceChain(fs):
        if fparent == a.symId:
          m.args.addParLe OconvT, m.argInfo
          m.args.addIntLit diff, m.argInfo
          inc m.inheritanceCosts, diff
          inc m.opened
          diff = 0 # mark as success
          break
        inc diff
      if diff != 0:
        m.error expected(f, a)
      elif m.skippedMod == OutM:
        m.error "subtype relation not available for `out` parameters"
  elif isConcept(fs):
    m.error "'concept' is not implemented"
  else:
    # fast check that works for aliases too:
    if a.kind == Symbol and a.symId == fs:
      discard "perfect match"
    else:
      var impl = asTypeAlias(fs)
      if impl.kind == ParLe and impl.tagId == ErrT:
        # not a type alias!
        m.error expected(f, a)
      else:
        singleArg(m, impl, arg)

proc cmpTypeBits(f, a: Cursor): int =
  if (f.kind == IntLit or f.kind == InlineInt) and
     (a.kind == IntLit or a.kind == InlineInt):
    result = typebits(f.load) - typebits(a.load)
  else:
    result = -1

proc matchIntegralType(m: var Match; f: var Cursor; arg: ArgItem) =
  var a = skipModifier(arg.typ)
  if f.tag == a.tag:
    inc a
  else:
    m.error expected(f, a)
    return
  inc f
  let cmp = cmpTypeBits(f, a)
  if cmp == 0:
    discard "same types"
  elif cmp > 0:
    # f has more bits than a, great!
    if m.skippedMod in {MutM, OutM}:
      m.error "implicit conversion to " & toString(f) & " is not mutable"
    else:
      m.args.addParLe HconvT, m.argInfo
      inc m.intCosts
      inc m.opened
  else:
    m.error expected(f, a)

proc expectParRi(m: var Match; f: var Cursor) =
  if f.kind == ParRi:
    inc f
  else:
    m.error "BUG: formal type not at end!"

proc singleArg(m: var Match; f: var Cursor; arg: ArgItem) =
  case f.kind
  of Symbol:
    matchSymbol m, f, arg
    inc f
  of ParLe:
    case f.tagId
    of MutT:
      var a = arg.typ
      if a.modtag in {MutM, OutM, LentM}:
        inc a
      else:
        m.skippedMod = f.modtag
        m.args.addParLe HaddrT, m.argInfo
        inc m.opened
      inc f
      singleArg m, f, ArgItem(n: arg.n, typ: a)
      expectParRi m, f
    of IT, UT, FT, CT:
      matchIntegralType m, f, arg
      expectParRi m, f
    of BoolT:
      var a = skipModifier(arg.typ)
      if a.tag != BoolT:
        m.error expected(f, a)
      expectParRi m, f
    of InvokT:
      # Keep in mind that (invok GenericHead Type1 Type2 ...)
      # is tyGenericInvokation in the old Nim. A generic *instance*
      # is always a nominal type ("Symbol") like
      # `(type GeneratedName (invok MyInst ConcreteTypeA ConcreteTypeB) (object ...))`.
      # This means a Symbol can match an InvokT.
      var a = skipModifier(arg.typ)
      if a.kind == Symbol:
        var t = asTypeDecl(a)
        if t.typevars.tag == InvokT:
          linearMatch m, f, t.typevars
        else:
          m.error expected(f, a)
      else:
        linearMatch m, f, a
      expectParRi m, f
    of ArrayT:
      var a = skipModifier(arg.typ)
      linearMatch m, f, a
      expectParRi m, f
    else:
      m.error "BUG: unhandled type: " & pool.tags[f.tagId]
  else:
    m.error "BUG: " & expected(f, arg.typ)

  if not m.err:
    m.useArg arg # since it was a match, copy it
    while m.opened > 0:
      m.args.addParRi()
      dec m.opened

proc sigmatchLoop(m: var Match; f: var Cursor; args: openArray[ArgItem]) =
  var i = 0
  while i < args.len and f.kind != ParRi:
    m.skippedMod = NoneM
    m.argInfo = args[i].n.info
    singleArg m, f, args[i]
    if m.err: break
    inc m.pos
    inc i


iterator typeVars(fn: SymId): SymId =
  let buf = loadSym(fn)
  var c = beginRead(buf[])
  if isRoutine(c.tag):
    inc c # skip routine tag
    for i in 1..3:
      skip c # name, export marker, pattern
    if c.tag == TypeVarsT:
      while c.kind != ParRi:
        if c.tag == TypeVarT:
          var tv = c
          inc tv
          yield tv.symId
        skip c

proc collectDefaultValues(f: var Cursor): seq[ArgItem] =
  result = @[]
  while f.tag == ParamT:
    let param = asLocal(f)
    result.add ArgItem(n: param.val, typ: param.typ)
    skip f

proc sigmatch*(m: var Match; fn: ArgItem; args: openArray[ArgItem];
               explicitTypeVars: Cursor) =
  m.tvars = initHashSet[SymId]()
  if fn.n.kind == Symbol:
    var e = explicitTypeVars
    for v in typeVars(fn.n.symId):
      m.tvars.incl v
      if e.kind != DotToken and e.kind != ParRi:
        m.inferred[v] = e
        skip e

  if explicitTypeVars.kind != DotToken:
    # aka there are explicit type vars
    if m.tvars.len == 0:
      m.error "routine is not generic"
      return

  var f = fn.typ
  sigmatchLoop m, f, args

  if m.pos < args.len:
    # not all arguments where used, error:
    m.error "too many arguments"
  elif f.kind != ParRi:
    # use default values for these parameters, but this needs to be done
    # properly with generics etc. so we use a helper `args` seq and pretend
    # the programmer had written out these arguments:
    let moreArgs = collectDefaultValues(f)
    sigmatchLoop m, f, moreArgs
    if f.kind != ParRi:
      m.error "too many parameters"

  # check all type vars have a value:
  if not m.err and fn.n.kind == Symbol:
    for v in typeVars(fn.n.symId):
      let inf = m.inferred.getOrDefault(v)
      if inf == default(Cursor):
        m.error "could not infer type for " & pool.syms[v]
        break
      m.typeArgs.addSubtree inf

proc matchesBool*(m: var Match; t: Cursor) =
  var a = skipModifier(t)
  if a.tag == BoolT:
    inc a
    if a.kind == ParRi: return
  m.error concat("expected: 'bool' but got: ", toString(t))

# How to implement named parameters: In a preprocessing step
# The signature is matched against the named parameters. The
# call is then reordered to `f`'s needs. This keeps the common case fast
# where no named parameters are used at all.

