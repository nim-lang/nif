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
    # only add final child unless final child is `.`, in which case delete completely
    var last = c
    inc c
    if c.kind == ParRi:
      inc c
      return
    while c.kind != ParRi:
      last = c
      skip c
    if last.kind == DotToken:
      inc last
    else:
      addWithoutErrorsImpl(result, last)
    assert last == c
    inc c
  else:
    var nested = 0
    while true:
      let item = c.load
      if item.kind == ParRi:
        result.add item
        dec nested
        inc c
        if nested == 0: break
      elif item.kind == ParLe:
        if item.tagId == ErrT:
          addWithoutErrorsImpl(result, c)
        else:
          result.add item
          inc nested
          inc c

proc addWithoutErrors*(result: var TokenBuf, c: Cursor) =
  var c = c
  addWithoutErrorsImpl(result, c)
