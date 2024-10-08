# GENERATED BY NifGram. DO NOT EDIT!
# ORIGINAL FILE: src/nifc/preasm/preasm_grammar.nif
proc matchExpr(c: var Context; it: var Item): bool
proc matchCallingConvention(c: var Context; it: var Item): bool
proc matchVarPragmas(c: var Context; it: var Item): bool
proc matchParamPragmas(c: var Context; it: var Item): bool
proc matchProcPragmas(c: var Context; it: var Item): bool



proc matchIntType(c: var Context; it: var Item): bool =
  when declared(handleIntType):
    var before1 = save(c, it)
  var kw2 = false
  if isTag(c, it, IT):
    if not matchIntLit(c, it):
      error(c, it, "INTLIT expected")
      return false
    discard matchIntLit(c, it)
    kw2 = matchParRi(c, it)
  if not kw2: return false
  when declared(handleIntType):
    handleIntType(c, it, before1)
  return true

proc matchUIntType(c: var Context; it: var Item): bool =
  when declared(handleUIntType):
    var before1 = save(c, it)
  var kw2 = false
  if isTag(c, it, UT):
    if not matchIntLit(c, it):
      error(c, it, "INTLIT expected")
      return false
    discard matchIntLit(c, it)
    kw2 = matchParRi(c, it)
  if not kw2: return false
  when declared(handleUIntType):
    handleUIntType(c, it, before1)
  return true

proc matchFloatType(c: var Context; it: var Item): bool =
  when declared(handleFloatType):
    var before1 = save(c, it)
  var kw2 = false
  if isTag(c, it, FT):
    if not matchIntLit(c, it):
      error(c, it, "INTLIT expected")
      return false
    discard matchIntLit(c, it)
    kw2 = matchParRi(c, it)
  if not kw2: return false
  when declared(handleFloatType):
    handleFloatType(c, it, before1)
  return true

proc matchMemType(c: var Context; it: var Item): bool =
  when declared(handleMemType):
    var before1 = save(c, it)
  var kw2 = false
  if isTag(c, it, MT):
    if not matchIntLit(c, it):
      error(c, it, "INTLIT expected")
      return false
    discard matchIntLit(c, it)
    kw2 = matchParRi(c, it)
  if not kw2: return false
  when declared(handleMemType):
    handleMemType(c, it, before1)
  return true

proc matchBoolType(c: var Context; it: var Item): bool =
  when declared(handleBoolType):
    var before1 = save(c, it)
  if not isTag(c, it, BT): return false
  when declared(handleBoolType):
    handleBoolType(c, it, before1)
  return true

proc matchType(c: var Context; it: var Item): bool =
  when declared(handleType):
    var before1 = save(c, it)
  var or2 = false
  block or3:
    if matchIntType(c, it):
      or2 = true
      break or3
    if matchUIntType(c, it):
      or2 = true
      break or3
    if matchFloatType(c, it):
      or2 = true
      break or3
    if matchMemType(c, it):
      or2 = true
      break or3
    if matchBoolType(c, it):
      or2 = true
      break or3
  if not or2: return false
  when declared(handleType):
    handleType(c, it, before1)
  return true

proc matchLvalue(c: var Context; it: var Item): bool =
  when declared(handleLvalue):
    var before1 = save(c, it)
  var or2 = false
  block or3:
    if lookupSym(c, it):
      or2 = true
      break or3
    var kw4 = false
    if isTag(c, it, LoadT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw4 = matchParRi(c, it)
    if kw4:
      or2 = true
      break or3
  if not or2: return false
  when declared(handleLvalue):
    handleLvalue(c, it, before1)
  return true

proc matchCall(c: var Context; it: var Item): bool =
  when declared(handleCall):
    var before1 = save(c, it)
  var kw2 = false
  if isTag(c, it, CallT):
    if not matchType(c, it):
      error(c, it, "Type expected")
      return false
    if not matchCallingConvention(c, it):
      error(c, it, "CallingConvention expected")
      return false
    var or3 = false
    block or4:
      if matchEmpty(c, it):
        or3 = true
        break or4
      if isTag(c, it, VarargsT):
        or3 = true
        break or4
    if not or3:
      error(c, it, "invalid Call")
      return false
    var om5 = false
    while not peekParRi(c, it):
      if not matchExpr(c, it):
        break
      else:
        om5 = true
    if not om5:
      error(c, it, "invalid Call")
      return false
    kw2 = matchParRi(c, it)
  if not kw2: return false
  when declared(handleCall):
    handleCall(c, it, before1)
  return true

proc matchExpr(c: var Context; it: var Item): bool =
  when declared(handleExpr):
    var before1 = save(c, it)
  var or2 = false
  block or3:
    if matchIntLit(c, it):
      or2 = true
      break or3
    if matchUIntLit(c, it):
      or2 = true
      break or3
    if matchFloatLit(c, it):
      or2 = true
      break or3
    if matchCharLit(c, it):
      or2 = true
      break or3
    if matchLvalue(c, it):
      or2 = true
      break or3
    var kw4 = false
    if isTag(c, it, VaddrT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not lookupSym(c, it):
        error(c, it, "SYMBOL expected")
        break or3
      kw4 = matchParRi(c, it)
    if kw4:
      or2 = true
      break or3
    var kw5 = false
    if isTag(c, it, GaddrT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not lookupSym(c, it):
        error(c, it, "SYMBOL expected")
        break or3
      kw5 = matchParRi(c, it)
    if kw5:
      or2 = true
      break or3
    var kw6 = false
    if isTag(c, it, TaddrT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not lookupSym(c, it):
        error(c, it, "SYMBOL expected")
        break or3
      kw6 = matchParRi(c, it)
    if kw6:
      or2 = true
      break or3
    var kw7 = false
    if isTag(c, it, NotT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw7 = matchParRi(c, it)
    if kw7:
      or2 = true
      break or3
    var kw8 = false
    if isTag(c, it, NegT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw8 = matchParRi(c, it)
    if kw8:
      or2 = true
      break or3
    var kw9 = false
    if isTag(c, it, AddscaledT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw9 = matchParRi(c, it)
    if kw9:
      or2 = true
      break or3
    var kw10 = false
    if isTag(c, it, AddT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw10 = matchParRi(c, it)
    if kw10:
      or2 = true
      break or3
    var kw11 = false
    if isTag(c, it, SubT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw11 = matchParRi(c, it)
    if kw11:
      or2 = true
      break or3
    var kw12 = false
    if isTag(c, it, MulT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw12 = matchParRi(c, it)
    if kw12:
      or2 = true
      break or3
    var kw13 = false
    if isTag(c, it, DivT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw13 = matchParRi(c, it)
    if kw13:
      or2 = true
      break or3
    var kw14 = false
    if isTag(c, it, ModT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw14 = matchParRi(c, it)
    if kw14:
      or2 = true
      break or3
    var kw15 = false
    if isTag(c, it, ShrT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw15 = matchParRi(c, it)
    if kw15:
      or2 = true
      break or3
    var kw16 = false
    if isTag(c, it, ShlT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw16 = matchParRi(c, it)
    if kw16:
      or2 = true
      break or3
    var kw17 = false
    if isTag(c, it, BitandT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw17 = matchParRi(c, it)
    if kw17:
      or2 = true
      break or3
    var kw18 = false
    if isTag(c, it, BitorT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw18 = matchParRi(c, it)
    if kw18:
      or2 = true
      break or3
    var kw19 = false
    if isTag(c, it, BitnotT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw19 = matchParRi(c, it)
    if kw19:
      or2 = true
      break or3
    var kw20 = false
    if isTag(c, it, BitxorT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw20 = matchParRi(c, it)
    if kw20:
      or2 = true
      break or3
    var kw21 = false
    if isTag(c, it, EqT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw21 = matchParRi(c, it)
    if kw21:
      or2 = true
      break or3
    var kw22 = false
    if isTag(c, it, NeqT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw22 = matchParRi(c, it)
    if kw22:
      or2 = true
      break or3
    var kw23 = false
    if isTag(c, it, LeT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw23 = matchParRi(c, it)
    if kw23:
      or2 = true
      break or3
    var kw24 = false
    if isTag(c, it, LtT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw24 = matchParRi(c, it)
    if kw24:
      or2 = true
      break or3
    var kw25 = false
    if isTag(c, it, SextT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw25 = matchParRi(c, it)
    if kw25:
      or2 = true
      break or3
    var kw26 = false
    if isTag(c, it, ZextT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw26 = matchParRi(c, it)
    if kw26:
      or2 = true
      break or3
    var kw27 = false
    if isTag(c, it, FextT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw27 = matchParRi(c, it)
    if kw27:
      or2 = true
      break or3
    var kw28 = false
    if isTag(c, it, FnarrowT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw28 = matchParRi(c, it)
    if kw28:
      or2 = true
      break or3
    var kw29 = false
    if isTag(c, it, TruncT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw29 = matchParRi(c, it)
    if kw29:
      or2 = true
      break or3
    var kw30 = false
    if isTag(c, it, FtoiT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw30 = matchParRi(c, it)
    if kw30:
      or2 = true
      break or3
    var kw31 = false
    if isTag(c, it, FtouT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw31 = matchParRi(c, it)
    if kw31:
      or2 = true
      break or3
    var kw32 = false
    if isTag(c, it, ItofT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw32 = matchParRi(c, it)
    if kw32:
      or2 = true
      break or3
    var kw33 = false
    if isTag(c, it, UtofT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw33 = matchParRi(c, it)
    if kw33:
      or2 = true
      break or3
    if matchCall(c, it):
      or2 = true
      break or3
  if not or2: return false
  when declared(handleExpr):
    handleExpr(c, it, before1)
  return true

proc matchVarDeclCommon(c: var Context; it: var Item): bool =
  when declared(handleVarDeclCommon):
    var before1 = save(c, it)
  var sym2 = declareSym(c, it)
  if not success(sym2): return false
  if not matchVarPragmas(c, it): return false
  if not matchType(c, it): return false
  when declared(handleVarDeclCommon):
    handleVarDeclCommon(c, it, before1)
  return true

proc matchVarDecl(c: var Context; it: var Item): bool =
  when declared(handleVarDecl):
    var before1 = save(c, it)
  var or2 = false
  block or3:
    var kw4 = false
    if isTag(c, it, VarT):
      if not matchVarDeclCommon(c, it):
        error(c, it, "VarDeclCommon expected")
        break or3
      kw4 = matchParRi(c, it)
    if kw4:
      or2 = true
      break or3
    var kw5 = false
    if isTag(c, it, GvarT):
      if not matchVarDeclCommon(c, it):
        error(c, it, "VarDeclCommon expected")
        break or3
      kw5 = matchParRi(c, it)
    if kw5:
      or2 = true
      break or3
    var kw6 = false
    if isTag(c, it, TvarT):
      if not matchVarDeclCommon(c, it):
        error(c, it, "VarDeclCommon expected")
        break or3
      kw6 = matchParRi(c, it)
    if kw6:
      or2 = true
      break or3
  if not or2: return false
  when declared(handleVarDecl):
    handleVarDecl(c, it, before1)
  return true

proc matchConstBody(c: var Context; it: var Item): bool =
  when declared(handleConstBody):
    var before1 = save(c, it)
  var kw2 = false
  if isTag(c, it, ValuesT):
    var om3 = false
    while not peekParRi(c, it):
      var or4 = false
      block or5:
        if lookupSym(c, it):
          or4 = true
          break or5
        if matchIntLit(c, it):
          or4 = true
          break or5
        if matchUIntLit(c, it):
          or4 = true
          break or5
        if matchFloatLit(c, it):
          or4 = true
          break or5
        if matchCharLit(c, it):
          or4 = true
          break or5
      if not or4:
        break
      else:
        om3 = true
    if not om3:
      error(c, it, "invalid ConstBody")
      return false
    kw2 = matchParRi(c, it)
  if not kw2: return false
  when declared(handleConstBody):
    handleConstBody(c, it, before1)
  return true

proc matchConstDecl(c: var Context; it: var Item): bool =
  when declared(handleConstDecl):
    var before1 = save(c, it)
  var kw2 = false
  if isTag(c, it, ConstT):
    var sym3 = declareSym(c, it)
    if not success(sym3):
      error(c, it, "SYMBOLDEF expected")
      return false
    if not matchVarPragmas(c, it):
      error(c, it, "VarPragmas expected")
      return false
    if not matchType(c, it):
      error(c, it, "Type expected")
      return false
    if not matchConstBody(c, it):
      error(c, it, "ConstBody expected")
      return false
    kw2 = matchParRi(c, it)
  if not kw2: return false
  when declared(handleConstDecl):
    handleConstDecl(c, it, before1)
  return true

proc matchAsciizDecl(c: var Context; it: var Item): bool =
  when declared(handleAsciizDecl):
    var before1 = save(c, it)
  var kw2 = false
  if isTag(c, it, AsciizT):
    var sym3 = declareSym(c, it)
    if not success(sym3):
      error(c, it, "SYMBOLDEF expected")
      return false
    if not matchStringlit(c, it):
      error(c, it, "STRINGLITERAL expected")
      return false
    kw2 = matchParRi(c, it)
  if not kw2: return false
  when declared(handleAsciizDecl):
    handleAsciizDecl(c, it, before1)
  return true

proc matchEmitStmt(c: var Context; it: var Item): bool =
  when declared(handleEmitStmt):
    var before1 = save(c, it)
  var kw2 = false
  if isTag(c, it, EmitT):
    var om3 = false
    while not peekParRi(c, it):
      if not matchExpr(c, it):
        break
      else:
        om3 = true
    if not om3:
      error(c, it, "invalid EmitStmt")
      return false
    kw2 = matchParRi(c, it)
  if not kw2: return false
  when declared(handleEmitStmt):
    handleEmitStmt(c, it, before1)
  return true

proc matchStmt(c: var Context; it: var Item): bool =
  when declared(handleStmt):
    var before1 = save(c, it)
  var or2 = false
  block or3:
    if matchCall(c, it):
      or2 = true
      break or3
    if matchVarDecl(c, it):
      or2 = true
      break or3
    if matchEmitStmt(c, it):
      or2 = true
      break or3
    var kw4 = false
    if isTag(c, it, AsgnT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchLvalue(c, it):
        error(c, it, "Lvalue expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw4 = matchParRi(c, it)
    if kw4:
      or2 = true
      break or3
    var kw5 = false
    if isTag(c, it, StoreT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchLvalue(c, it):
        error(c, it, "Lvalue expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw5 = matchParRi(c, it)
    if kw5:
      or2 = true
      break or3
    var kw6 = false
    if isTag(c, it, LabT):
      var sym7 = declareSym(c, it)
      if not success(sym7):
        error(c, it, "SYMBOLDEF expected")
        break or3
      kw6 = matchParRi(c, it)
    if kw6:
      or2 = true
      break or3
    var kw8 = false
    if isTag(c, it, LoopT):
      var sym9 = declareSym(c, it)
      if not success(sym9):
        error(c, it, "SYMBOLDEF expected")
        break or3
      kw8 = matchParRi(c, it)
    if kw8:
      or2 = true
      break or3
    var kw10 = false
    if isTag(c, it, TjmpT):
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      if not lookupSym(c, it):
        error(c, it, "SYMBOL expected")
        break or3
      kw10 = matchParRi(c, it)
    if kw10:
      or2 = true
      break or3
    var kw11 = false
    if isTag(c, it, FjmpT):
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      if not lookupSym(c, it):
        error(c, it, "SYMBOL expected")
        break or3
      kw11 = matchParRi(c, it)
    if kw11:
      or2 = true
      break or3
    var kw12 = false
    if isTag(c, it, JmpT):
      if not lookupSym(c, it):
        error(c, it, "SYMBOL expected")
        break or3
      kw12 = matchParRi(c, it)
    if kw12:
      or2 = true
      break or3
    var kw13 = false
    if isTag(c, it, JloopT):
      if not lookupSym(c, it):
        error(c, it, "SYMBOL expected")
        break or3
      kw13 = matchParRi(c, it)
    if kw13:
      or2 = true
      break or3
    var kw14 = false
    if isTag(c, it, RetT):
      if not matchType(c, it):
        error(c, it, "Type expected")
        break or3
      if not matchExpr(c, it):
        error(c, it, "Expr expected")
        break or3
      kw14 = matchParRi(c, it)
    if kw14:
      or2 = true
      break or3
  if not or2: return false
  when declared(handleStmt):
    handleStmt(c, it, before1)
  return true

proc matchStmtList(c: var Context; it: var Item): bool =
  when declared(handleStmtList):
    var before1 = save(c, it)
  var kw2 = false
  if isTag(c, it, StmtsT):
    var zm3 = true
    while not peekParRi(c, it):
      if not matchStmt(c, it):
        zm3 = false
        break
    if not zm3:
      error(c, it, "invalid StmtList")
      return false
    kw2 = matchParRi(c, it)
  if not kw2: return false
  when declared(handleStmtList):
    handleStmtList(c, it, before1)
  return true

proc matchParam(c: var Context; it: var Item): bool =
  when declared(handleParam):
    var before1 = save(c, it)
  var kw2 = false
  if isTag(c, it, ParamT):
    var sym3 = declareSym(c, it)
    if not success(sym3):
      error(c, it, "SYMBOLDEF expected")
      return false
    if not matchParamPragmas(c, it):
      error(c, it, "ParamPragmas expected")
      return false
    if not matchType(c, it):
      error(c, it, "Type expected")
      return false
    kw2 = matchParRi(c, it)
  if not kw2: return false
  when declared(handleParam):
    handleParam(c, it, before1)
  return true

proc matchParams(c: var Context; it: var Item): bool =
  when declared(handleParams):
    var before1 = save(c, it)
  var or2 = false
  block or3:
    if matchEmpty(c, it):
      or2 = true
      break or3
    var zm4 = true
    while not peekParRi(c, it):
      var kw5 = false
      if isTag(c, it, ParamsT):
        if not matchParam(c, it):
          error(c, it, "Param expected")
          break or3
        kw5 = matchParRi(c, it)
      if not kw5:
        zm4 = false
        break
    if zm4:
      or2 = true
      break or3
  if not or2: return false
  when declared(handleParams):
    handleParams(c, it, before1)
  return true

proc matchProcDecl(c: var Context; it: var Item): bool =
  when declared(handleProcDecl):
    var before1 = save(c, it)
  var kw2 = false
  if isTag(c, it, ProcT):
    var sym3 = declareSym(c, it)
    if not success(sym3):
      error(c, it, "SYMBOLDEF expected")
      return false
    if not matchParams(c, it):
      error(c, it, "Params expected")
      return false
    if not matchType(c, it):
      error(c, it, "Type expected")
      return false
    if not matchProcPragmas(c, it):
      error(c, it, "ProcPragmas expected")
      return false
    var or4 = false
    block or5:
      if matchEmpty(c, it):
        or4 = true
        break or5
      if matchStmtList(c, it):
        or4 = true
        break or5
    if not or4:
      error(c, it, "invalid ProcDecl")
      return false
    kw2 = matchParRi(c, it)
  if not kw2: return false
  when declared(handleProcDecl):
    handleProcDecl(c, it, before1)
  return true

proc matchCallingConvention(c: var Context; it: var Item): bool =
  when declared(handleCallingConvention):
    var before1 = save(c, it)
  var or2 = false
  block or3:
    if isTag(c, it, CdeclT):
      or2 = true
      break or3
    if isTag(c, it, StdcallT):
      or2 = true
      break or3
    if isTag(c, it, SafecallT):
      or2 = true
      break or3
    if isTag(c, it, SyscallT):
      or2 = true
      break or3
    if isTag(c, it, FastcallT):
      or2 = true
      break or3
    if isTag(c, it, ThiscallT):
      or2 = true
      break or3
    if isTag(c, it, NoconvT):
      or2 = true
      break or3
    if isTag(c, it, MemberT):
      or2 = true
      break or3
  if not or2: return false
  when declared(handleCallingConvention):
    handleCallingConvention(c, it, before1)
  return true

proc matchAttribute(c: var Context; it: var Item): bool =
  when declared(handleAttribute):
    var before1 = save(c, it)
  var kw2 = false
  if isTag(c, it, AttrT):
    if not matchStringlit(c, it):
      error(c, it, "STRINGLITERAL expected")
      return false
    kw2 = matchParRi(c, it)
  if not kw2: return false
  when declared(handleAttribute):
    handleAttribute(c, it, before1)
  return true

proc matchIdentifier(c: var Context; it: var Item): bool =
  when declared(handleIdentifier):
    var before1 = save(c, it)
  var or2 = false
  block or3:
    if lookupSym(c, it):
      or2 = true
      break or3
    if matchIdent(c, it):
      or2 = true
      break or3
  if not or2: return false
  when declared(handleIdentifier):
    handleIdentifier(c, it, before1)
  return true

proc matchProcPragma(c: var Context; it: var Item): bool =
  when declared(handleProcPragma):
    var before1 = save(c, it)
  var or2 = false
  block or3:
    if matchCallingConvention(c, it):
      or2 = true
      break or3
    if isTag(c, it, VarargsT):
      or2 = true
      break or3
    var kw4 = false
    if isTag(c, it, WasT):
      if not matchIdentifier(c, it):
        error(c, it, "Identifier expected")
        break or3
      kw4 = matchParRi(c, it)
    if kw4:
      or2 = true
      break or3
    if isTag(c, it, SelectanyT):
      or2 = true
      break or3
    if matchAttribute(c, it):
      or2 = true
      break or3
  if not or2: return false
  when declared(handleProcPragma):
    handleProcPragma(c, it, before1)
  return true

proc matchProcPragmas(c: var Context; it: var Item): bool =
  when declared(handleProcPragmas):
    var before1 = save(c, it)
  var or2 = false
  block or3:
    if matchEmpty(c, it):
      or2 = true
      break or3
    var kw4 = false
    if isTag(c, it, PragmasT):
      var om5 = false
      while not peekParRi(c, it):
        if not matchProcPragma(c, it):
          break
        else:
          om5 = true
      if not om5:
        error(c, it, "invalid ProcPragmas")
        break or3
      kw4 = matchParRi(c, it)
    if kw4:
      or2 = true
      break or3
  if not or2: return false
  when declared(handleProcPragmas):
    handleProcPragmas(c, it, before1)
  return true

proc matchCommonPragma(c: var Context; it: var Item): bool =
  when declared(handleCommonPragma):
    var before1 = save(c, it)
  var or2 = false
  block or3:
    var kw4 = false
    if isTag(c, it, AlignT):
      if not matchIntLit(c, it):
        error(c, it, "INTLIT expected")
        break or3
      kw4 = matchParRi(c, it)
    if kw4:
      or2 = true
      break or3
    var kw5 = false
    if isTag(c, it, WasT):
      if not matchIdentifier(c, it):
        error(c, it, "Identifier expected")
        break or3
      kw5 = matchParRi(c, it)
    if kw5:
      or2 = true
      break or3
    if matchAttribute(c, it):
      or2 = true
      break or3
  if not or2: return false
  when declared(handleCommonPragma):
    handleCommonPragma(c, it, before1)
  return true

proc matchVarPragma(c: var Context; it: var Item): bool =
  when declared(handleVarPragma):
    var before1 = save(c, it)
  if not matchCommonPragma(c, it): return false
  when declared(handleVarPragma):
    handleVarPragma(c, it, before1)
  return true

proc matchVarPragmas(c: var Context; it: var Item): bool =
  when declared(handleVarPragmas):
    var before1 = save(c, it)
  var or2 = false
  block or3:
    if matchEmpty(c, it):
      or2 = true
      break or3
    var kw4 = false
    if isTag(c, it, PragmasT):
      var om5 = false
      while not peekParRi(c, it):
        if not matchVarPragma(c, it):
          break
        else:
          om5 = true
      if not om5:
        error(c, it, "invalid VarPragmas")
        break or3
      kw4 = matchParRi(c, it)
    if kw4:
      or2 = true
      break or3
  if not or2: return false
  when declared(handleVarPragmas):
    handleVarPragmas(c, it, before1)
  return true

proc matchParamPragma(c: var Context; it: var Item): bool =
  when declared(handleParamPragma):
    var before1 = save(c, it)
  var or2 = false
  block or3:
    var kw4 = false
    if isTag(c, it, WasT):
      if not matchIdentifier(c, it):
        error(c, it, "Identifier expected")
        break or3
      kw4 = matchParRi(c, it)
    if kw4:
      or2 = true
      break or3
    if matchAttribute(c, it):
      or2 = true
      break or3
  if not or2: return false
  when declared(handleParamPragma):
    handleParamPragma(c, it, before1)
  return true

proc matchParamPragmas(c: var Context; it: var Item): bool =
  when declared(handleParamPragmas):
    var before1 = save(c, it)
  var or2 = false
  block or3:
    if matchEmpty(c, it):
      or2 = true
      break or3
    var kw4 = false
    if isTag(c, it, PragmasT):
      var om5 = false
      while not peekParRi(c, it):
        if not matchParamPragma(c, it):
          break
        else:
          om5 = true
      if not om5:
        error(c, it, "invalid ParamPragmas")
        break or3
      kw4 = matchParRi(c, it)
    if kw4:
      or2 = true
      break or3
  if not or2: return false
  when declared(handleParamPragmas):
    handleParamPragmas(c, it, before1)
  return true

proc matchExternDecl(c: var Context; it: var Item): bool =
  when declared(handleExternDecl):
    var before1 = save(c, it)
  var kw2 = false
  if isTag(c, it, ImpT):
    var or3 = false
    block or4:
      if matchProcDecl(c, it):
        or3 = true
        break or4
      if matchVarDecl(c, it):
        or3 = true
        break or4
      if matchConstDecl(c, it):
        or3 = true
        break or4
    if not or3:
      error(c, it, "invalid ExternDecl")
      return false
    kw2 = matchParRi(c, it)
  if not kw2: return false
  when declared(handleExternDecl):
    handleExternDecl(c, it, before1)
  return true

proc matchInclude(c: var Context; it: var Item): bool =
  when declared(handleInclude):
    var before1 = save(c, it)
  var kw2 = false
  if isTag(c, it, InclT):
    if not matchStringlit(c, it):
      error(c, it, "STRINGLITERAL expected")
      return false
    kw2 = matchParRi(c, it)
  if not kw2: return false
  when declared(handleInclude):
    handleInclude(c, it, before1)
  return true

proc matchTopLevelConstruct(c: var Context; it: var Item): bool =
  when declared(handleTopLevelConstruct):
    var before1 = save(c, it)
  var or2 = false
  block or3:
    if matchExternDecl(c, it):
      or2 = true
      break or3
    if matchProcDecl(c, it):
      or2 = true
      break or3
    if matchVarDecl(c, it):
      or2 = true
      break or3
    if matchConstDecl(c, it):
      or2 = true
      break or3
    if matchAsciizDecl(c, it):
      or2 = true
      break or3
    if matchInclude(c, it):
      or2 = true
      break or3
    if matchEmitStmt(c, it):
      or2 = true
      break or3
  if not or2: return false
  when declared(handleTopLevelConstruct):
    handleTopLevelConstruct(c, it, before1)
  return true

proc matchModule(c: var Context; it: var Item): bool =
  when declared(handleModule):
    var before1 = save(c, it)
  var kw2 = false
  if isTag(c, it, StmtsT):
    var zm3 = true
    while not peekParRi(c, it):
      if not matchTopLevelConstruct(c, it):
        zm3 = false
        break
    if not zm3:
      error(c, it, "invalid Module")
      return false
    kw2 = matchParRi(c, it)
  if not kw2: return false
  when declared(handleModule):
    handleModule(c, it, before1)
  return true
