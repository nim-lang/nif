#       Nif library
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Produces a Nim proc that maps a string to an enum value.
## This produces a binary tree search that is faster than
## hashing as hashing requires 2 passes over the string.

# We split the set of strings into 2 sets of roughly the same size.
# The condition used for splitting is a (position, char) tuple.
# Every string of length > position for which s[position] <= char is in one
# set else it is in the other set.

import std / [macros]

import stringviews

proc strAtLe(s: StringView; idx: int; ch: char): bool {.inline.} =
  result = idx < s.len and s[idx] <= ch

type
  Key = (string, string) # 2nd component is the enum field name as a string

func addUnique*[T](s: var seq[T]; x: T) =
  for y in items(s):
    if y == x: return
  s.add x

proc splitValue(a: openArray[Key]; position: int): (char, float) =
  var cand: seq[char] = @[]
  for t in items a:
    if t[0].len > position: cand.addUnique t[0][position]

  result = ('\0', -1.0)
  for disc in items cand:
    var hits = 0
    for t in items a:
      if t[0].len > position and t[0][position] <= disc:
        inc hits
    # the split is the better, the more `hits` is close to `a.len / 2`:
    let grade = 100000.0 - abs(hits.float - a.len.float / 2.0)
    if grade > result[1]:
      result = (disc, grade)

proc tryAllPositions(a: openArray[Key]): (char, int) =
  var m = 0
  for t in items a:
    m = max(m, t[0].len)

  result = ('\0', -1)
  var best = -1.0
  for i in 0 ..< m:
    let current = splitValue(a, i)
    if current[1] > best:
      best = current[1]
      result = (current[0], i)

type
  SearchKind = enum
    LinearSearch, SplitSearch
  SearchResult* = object
    case kind: SearchKind
    of LinearSearch:
      a: seq[Key]
    of SplitSearch:
      span: int
      best: (char, int)

proc emitLinearSearch(a: openArray[Key]; dest: var seq[SearchResult]) =
  var d = SearchResult(kind: LinearSearch, a: @[])
  for x in a: d.a.add x
  dest.add d

proc split(a: openArray[Key]; dest: var seq[SearchResult]) =
  if a.len <= 2:
    emitLinearSearch a, dest
  else:
    let best = tryAllPositions(a)
    var groupA: seq[Key] = @[]
    var groupB: seq[Key] = @[]
    for t in items a:
      if t[0].len > best[1] and t[0][best[1]] <= best[0]:
        groupA.add t
      else:
        groupB.add t
    if groupA.len == 0 or groupB.len == 0:
      emitLinearSearch a, dest
    else:
      let toPatch = dest.len
      dest.add SearchResult(kind: SplitSearch, span: 1, best: best)
      split groupA, dest
      split groupB, dest
      let dist = dest.len - toPatch
      assert dist > 0
      dest[toPatch].span = dist

proc decodeSolution(dest: NimNode; s: seq[SearchResult]; i: int;
                    selector: NimNode) =
  case s[i].kind
  of SplitSearch:
    let thenA = i+1
    let elseA = thenA + (if s[thenA].kind == LinearSearch: 1 else: s[thenA].span)
    let best = s[i].best

    var cond = newTree(nnkIfStmt)
    var elifBranch = newTree(nnkElifBranch)
    elifBranch.add newCall(bindSym"strAtLe", selector, newLit(best[1]), newLit(best[0]))

    decodeSolution elifBranch, s, thenA, selector

    var elseBranch = newTree(nnkElse)
    decodeSolution elseBranch, s, elseA, selector

    cond.add elifBranch
    cond.add elseBranch
    dest.add cond

  of LinearSearch:
    var cond = newTree(nnkIfStmt)
    for x in s[i].a:
      var elifBranch = newTree(nnkElifBranch)
      elifBranch.add newCall(bindSym"==", selector, newLit(x[0]))
      var action = newTree(nnkStmtList, newTree(nnkReturnStmt, ident(x[1])))
      elifBranch.add action
      cond.add elifBranch
    dest.add cond

proc genMatcher(body, selector: NimNode; a: openArray[Key]) =
  var solution: seq[SearchResult] = @[]
  split a, solution
  decodeSolution body, solution, 0, selector

macro declareMatcher*(name: untyped; e: typedesc): untyped =
  let typ = e.getTypeInst[1]
  let typSym = typ.getTypeImpl.getTypeInst # skip aliases etc to get type sym
  let impl = typSym.getImpl[2]
  expectKind impl, nnkEnumTy
  var fVal = ""
  var fStr = "" # string of current field

  var a: seq[Key] = @[]
  var i = 0
  for f in impl:
    inc i
    if i <= 2: continue # skip `low(e)`
    case f.kind
    of nnkEmpty: continue # skip first node of `enumTy`
    of nnkSym, nnkIdent:
      fVal = f.strVal
      fStr = fVal
    of nnkAccQuoted:
      fVal = ""
      for ch in f:
        fVal.add ch.strVal
      fStr = fVal
    of nnkEnumFieldDef:
      fVal = f[0].strVal
      case f[1].kind
      of nnkStrLit:
        fStr = f[1].strVal
      of nnkTupleConstr:
        fStr = f[1][1].strVal
      of nnkIntLit:
        fStr = f[0].strVal
      else:
        let fAst = f[0].getImpl
        if fAst.kind == nnkStrLit:
          fStr = fAst.strVal
        else:
          error("Invalid tuple syntax!", f[1])
    else: error("Invalid node for enum type `" & $f.kind & "`!", f)
    a.add (fStr, fVal)

  var body = newStmtList()
  genMatcher body, ident"sel", a

  echo repr body
  template t(name, body, e: untyped): untyped {.dirty.} =
    proc `name`(sel: StringView): e =
      body
      return low(e)
  result = getAst t(name, body, e)

when isMainModule:
  type
    MyEnum = enum
      UnknownValue, ValueA, ValueB = "value B", ValueC

  declareMatcher whichKeyword, MyEnum

  assert whichKeyword(toStringViewUnsafe"ValueC") == ValueC

  const
    AllKeys = ["alignas", "alignof", "and", "and_eq", "asm", "atomic_cancel", "atomic_commit",
     "atomic_noexcept", "auto",
     "bitand", "bitor", "bool", "break",
     "catch", "char", "char8_t", "char16_t", "char32_t", "class", "compl",
     "concept", "const", "consteval", "constexpr", "constinit", "const_cast", "continue",
     "co_await", "co_return", "co_yield",
     "decltype", "default", "delete", "do", "double", "dynamic_cast",
     "goto",
     "if", "inline", "int",
     "long",
     "main", "mutable",
     "namespace", "new", "noexcept", "not", "not_eq", "nullptr",
     "operator", "or", "or_eq",
     "private", "protected", "public",
     "reflexpr", "register", "reinterpret_cast", "requires", "return",
     "short", "signed", "sizeof", "static", "static_assert", "static_cast", "struct",
     "switch", "synchronized",
     "template", "this", "thread_local", "throw", "true", "try", "typedef",
     "typeid", "typename",
     "union", "unsigned", "using",
     "virtual", "void", "volatile",
     "wchar_t", "while",
     "xor", "xor_eq"]

  type
    CppKeyword = enum
      NoKeyword,
      alignas,
      alignof, andQ = "and", and_eq, asmQ = "asm", atomic_cancel, atomic_commit,
      atomic_noexcept, auto,
      bitand, bitor, bool, breakQ = "break",
      catch, char, char8_t, char16_t, char32_t, class, compl,
      conceptQ = "concept",
      constQ = "const", consteval, constexpr, constinit, const_cast,
      continueQ = "continue",
      co_await, co_return, co_yield,
      decltype, default, delete, doQ = "do", double, dynamic_cast,
      goto,
      ifQ = "if", inline, int,
      long,
      main, mutable,
      namespace, new, noexcept, notQ = "not", not_eq, nullptr,
      operator, orQ = "or", or_eq,
      private, protected, public,
      reflexpr, register, reinterpret_cast, requires, returnQ = "return",
      short, signed, sizeof, staticQ = "static", static_assert, static_cast, struct,
      switch, synchronized,
      templateQ = "template", this, thread_local, throw, trueQ = "true", tryQ = "try", typedef,
      typeid, typename,
      union, unsigned, usingQ = "using",
      virtual, void, volatile,
      wchar_t, whileQ = "while",
      xorQ = "xor", xor_eq

  declareMatcher whichCppKeyword, CppKeyword

  var i = 1
  for k in AllKeys:
    assert whichCppKeyword(toStringViewUnsafe(k)) == cast[CppKeyword](i)
    inc i
  assert whichCppKeyword(toStringViewUnsafe("u")) == NoKeyword
  assert whichCppKeyword(toStringViewUnsafe("")) == NoKeyword
  assert whichCppKeyword(toStringViewUnsafe("wusel")) == NoKeyword
