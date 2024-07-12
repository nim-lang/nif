#       Nif library
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## We like to traverse the implied AST by NIF without creating the AST
## as that it is expensive. We especially want to be able to skip subtrees.
## The solution is to traverse the file once and compute a skip table.

import nifreader, stringviews
import std / [strutils, algorithm, tables]

type
  SkipEntry = object
    offset, span: int32
  SkipTable = seq[SkipEntry]

proc `<`*(a, b: SkipEntry): bool = a.offset < b.offset
proc `==`*(a, b: SkipEntry): bool = a.offset == b.offset

proc myHex(x: int32): string =
  let x = toHex(x)
  var i = 0
  while i < x.len and x[i] == '0':
    inc i
  substr(x, i)

const
  Base36 = "0123456789abcdefghijklmnopqrstuvwxyz"

proc add*(result: var string; id: int32) =
  var id = id
  # Convert decimal number to base 36, reversed since it does not matter:
  while id > 0'i32:
    result.add Base36[int(id mod 36'i32)]
    id = id div 36'i32

proc `$`(e: SkipEntry): string =
  result = ""
  result.add e.offset
  result.add ":"
  result.add e.span
  #myHex(e.offset) & ":" & myHex(e.span)
  #$e.span

proc `$`(s: seq[SkipEntry]): string =
  result = ""
  var prev = 0'i32
  for e in s:
    result.add $(e.offset - prev)
    result.add ":"
    result.add $e.span
    result.add ','
    prev = e.offset
  when false:
    for x in e:
      result.add $x
      result.add ','

proc computeSkipTable*(r: var Reader; s: var SkipTable): int =
  result = offset(r)
  let t = next(r)
  #echo "LOOKGIN AT ", t
  case t.tk
  of EofToken:
    assert false
  of ParRi:
    result = -result
  of ParLe:
    let start = result
    var last = -1
    while true:
      last = computeSkipTable(r, s)
      if last < 0: break
    let span = (-last) - start
    if span > 128:
      # assumption: 2 cache lines is not worth storing
      s.add SkipEntry(offset: start.int32, span: span.int32)
  of UnknownToken, DotToken, Ident, Symbol, SymbolDef,
      StringLit, CharLit, IntLit, UIntLit, FloatLit:
    discard

type
  LazyNode* = object
    tk: TokenKind
    s: StringView
    file: StringView
    line, col: int32

  LazyTree* = object
    r: Reader
    skipTable: Table[int, StringView]

proc down*(tree: var LazyTree; n: LazyNode): LazyNode =
  # Node is always a compound node and after its tag we find the
  # "down" node.
  assert n.tk == ParLe
  setPosition(tree.r, n.s)
  let t = next(tree.r)
  if t.tk in {ParRi, EofToken}:
    return LazyNode(tk: t.tk, s: t.s)

  var line, col: int32
  if t.filename.len > 0:
    line = t.pos.line
    col = t.pos.col
  else:
    line = n.line + t.pos.line
    col = n.col + t.pos.col
  result = LazyNode(tk: t.tk, s: t.s, file: t.filename, line: line, col: col)

proc root*(tree: var LazyTree): LazyNode =
  let t = next(tree.r)
  assert t.tk notin {ParRi, EofToken}, "module has no root!"
  var line, col: int32
  if t.filename.len > 0:
    line = t.pos.line
    col = t.pos.col
  result = LazyNode(tk: t.tk, s: t.s, file: t.filename, line: line, col: col)

proc next*(tree: var LazyTree; n, parent: LazyNode): LazyNode =
  assert parent.tk == ParLe
  setPosition(tree.r, n.s)
  if n.tk == ParLe:
    # skip to ParRi
    let start = offset(tree.r)
    if tree.skipTable.len > 0:
      let dest = tree.skipTable.getOrDefault(start)
      if dest.len > 0:
        return LazyNode(tk: ParRi, s: dest)
    var stack: seq[(int, StringView)] = @[]
    var t = next(tree.r)
    while true:
      assert t.tk != EofToken, "missing ')'"
      if t.tk == ParRi:
        if stack.len == 0:
          t = next(tree.r) # skip the ')' and return whatever comes after:
          return LazyNode(tk: t.tk, s: t.s)
        let finished = stack.pop()
        t = next(tree.r)

        if span(tree.r, finished[0], t.s) > 128:
          # assumption: > 2 cache lines is worth storing
          tree.skipTable[finished[0]] = t.s
      else:
        if t.tk == ParLe:
          stack.add (offset(tree.r), StringView(p: nil, len: 0))
        t = next(tree.r)
  else:
    let t = next(tree.r)
    var line, col: int32
    if t.filename.len > 0:
      line = t.pos.line
      col = t.pos.col
    else:
      line = parent.line + t.pos.line
      col = parent.col + t.pos.col
    result = LazyNode(tk: t.tk, s: t.s, file: t.filename, line: line, col: col)

iterator sons(tree: var LazyTree; n: LazyNode): LazyNode =
  var child = down(tree, n)
  while child.tk != ParRi:
    yield child
    child = next(tree, child, n)

proc sons2*(tree: var LazyTree; n: LazyNode): (LazyNode, LazyNode) =
  let a = down(tree, n)
  let b = next(tree, a, n)
  (a, b)

proc traverse(tree: var LazyTree; n: LazyNode) =
  if n.tk == ParLe:
    echo "current head ", n.s
    if n.s == "asgn":
      echo "Found an assignment!"
      let (a, b) = sons2(tree, n)
      echo a.s, " = ", b.s
    else:
      for ch in sons(tree, n):
        traverse tree, ch
  else:
    echo "ignoring atom ", n.s


when isMainModule:

  const testData = """(.nif24)
(stmts
  (asgn (at x i) (call f a b))
  (call g x yz)
)
  """

  var tree = LazyTree(r: openFromBuffer(testData))
  let res = processDirectives(tree.r)
  echo res
  let r = root(tree)
  traverse tree, r
  echo "new round:"
  traverse tree, r


when false:
  import std / [strutils, monotimes]

  template bench(task, body) =
    let t0 = getMonoTime()
    body
    echo task, " TOOK ", getMonoTime() - t0

  proc test*(filename: string) =
    echo "A MEM: ", formatSize getOccupiedMem()

    var r = nifreader.open(filename)

    echo "B MEM: ", formatSize getOccupiedMem()

    bench "initial load":
      let res = processDirectives(r)
      echo res

    echo "C MEM: ", formatSize getOccupiedMem()

    assert res == Success
    var s: SkipTable = @[]
    bench "SkipTable":
      discard computeSkipTable(r, s)
      echo "D MEM: ", formatSize getOccupiedMem()
      algorithm.sort s
      echo s
      echo "In bytes: ", ($s).len
      echo "as binary: ", s.len * sizeof(SkipEntry)
    echo "ENTRIES: ", s.len

    echo "AToms ", atoms, " TRees ", trees

  test "tests/data/ccgexprs.nif"

