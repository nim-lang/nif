#       Nif library
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Do not use. Instead use the `nifreader` directly.

import nifreader

type
  NifTree* = ref object
    tok*: Token
    down*, next*: NifTree

proc parse*(r: var Reader; t: sink Token): NifTree =
  case t.tk
  of EofToken, ParRi:
    result = nil
  of ParLe:
    result = NifTree(tok: ensureMove t)
    var append {.cursor.} = result
    while true:
      let x = next(r)
      if x.tk in {EofToken, ParRi}: break
      let child = parse(r, x)
      assert child != nil
      if append == result:
        append.down = child
      else:
        append.next = child
      append = child
  of UnknownToken, DotToken, Ident, Symbol, SymbolDef,
      StringLit, CharLit, IntLit, UIntLit, FloatLit:
    result = NifTree(tok: ensureMove t)
