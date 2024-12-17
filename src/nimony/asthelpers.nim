## helpers specific to nimony AST

import std/assertions
include nifprelude

proc addWithoutErrorsImpl(result: var TokenBuf; c: var Cursor) =
  assert c.kind != ParRi, "cursor at end?"
  if c.kind != ParLe:
    # atom:
    result.add c.load
    inc c
  elif c.tagId == ErrT:
    var last = c
    inc c
    if c.kind == ParRi:
      inc c
      return
    while c.kind != ParRi:
      last = c
      skip c
    addWithoutErrorsImpl(result, last)
    assert last == c
    inc c
  else:
    var nested = 0
    while true:
      let item = c.load
      result.add item
      if item.kind == ParRi:
        dec nested
        inc c
        if nested == 0: break
      elif item.kind == ParLe:
        if item.tagId == ErrT:
          addWithoutErrorsImpl(result, c)
        else:
          inc nested
          inc c

proc addWithoutErrors*(result: var TokenBuf, c: Cursor) =
  var c = c
  addWithoutErrorsImpl(result, c)
