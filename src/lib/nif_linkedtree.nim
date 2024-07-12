#       Nif library
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Do not use. Instead use the `nifreader` directly.

import nifreader, arenas

type
  NifDesc* = object
    tok*: Token
    down*, next*: ptr NifDesc
  NifTree* = ptr NifDesc

var nodeAlloc* = createArena[NifDesc]()

proc newNode*(t: sink Token): NifTree =
  result = nodeAlloc.new[:NifDesc]()
  result.down = nil
  result.next = nil
  result.tok = ensureMove t

proc parse*(r: var Reader): NifTree =
  let t = next(r)
  case t.tk
  of EofToken, ParRi:
    result = nil
  of ParLe:
    result = newNode(t)
    var append {.cursor.} = result
    while true:
      let child = parse(r)
      if child == nil: break
      if append == result:
        append.down = child
      else:
        append.next = child
      append = child
  of UnknownToken, DotToken, Ident, Symbol, SymbolDef,
      StringLit, CharLit, IntLit, UIntLit, FloatLit:
    result = newNode(t)

proc toString(n: NifTree; result: var string; nesting: int) =
  if n != nil:
    result.add $n.tok
    var it {.cursor.} = n.down
    if it != nil:
      result.add "\n"
      for i in 0..<nesting-1: result.add ' '
    while it != nil:
      result.add ' '
      toString it, result, nesting+1
      it = it.next
    if n.tok.tk == ParLe:
      result.add ')'

proc `$`*(n: NifTree): string =
  result = ""
  toString(n, result, 1)
