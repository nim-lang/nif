#
#
#           NIFC Compiler
#        (c) Copyright 2024 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## Emits real ASM code from the NIF based format.

import nifreader, nifstreams, nifcursors, bitabs, lineinfos
from strutils import escape

import asm_model

type
  Context = object
    current: Cursor
    input: TokenBuf
    dest: string

proc fatal*(msg: string) =
  quit msg

proc setupInput(c: var Context; buffer: string) =
  var s = nifstreams.openFromBuffer(buffer)
  let res = processDirectives(s.r)
  assert res == Success
  c.input = default(TokenBuf)
  while true:
    let t = next(s)
    if t.kind == EofToken: break
    c.input.add t

proc matchIntLit(c: var Context): bool =
  if c.current.kind == IntLit:
    c.dest.addInt pool.integers[c.current.intId]
    inc c.current
    result = true
  else:
    result = false

proc matchUIntLit(c: var Context): bool =
  if c.current.kind == UIntLit:
    c.dest.add $pool.uintegers[c.current.uintId]
    inc c.current
    result = true
  else:
    result = false

proc matchFloatLit(c: var Context): bool =
  if c.current.kind == FloatLit:
    c.dest.add $pool.floats[c.current.floatId]
    inc c.current
    result = true
  else:
    result = false

proc matchStringLit(c: var Context): bool =
  if c.current.kind == StringLit:
    c.dest.add escape(pool.strings[c.current.litId])
    inc c.current
    result = true
  else:
    result = false

proc matchIdent(c: var Context): bool =
  if c.current.kind == Ident:
    c.dest.add pool.strings[c.current.litId]
    inc c.current
    result = true
  else:
    result = false

proc isTag(c: var Context; tag: TagId): bool =
  if c.current.kind == ParLe and c.current.tagId == tag:
    inc c.current
    result = true
  else:
    result = false

proc error(c: var Context; msg: string) =
  if c.current.info.isValid:
    let (f, line, col) = unpack(pool.man, c.current.info)
    echo "[Error] ", pool.files[f] & "(" & $line & ", " & $col & "): " & msg
  else:
    echo "[Error] ???: " & msg
  quit 1

proc matchParRi(c: var Context): bool =
  if c.current.kind == ParRi:
    inc c.current
    result = true
  else:
    result = false

proc peekParRi(c: var Context): bool {.inline.} =
  c.current.kind == ParRi

proc emitTag(c: var Context; tag: string) =
  c.dest.add tag
  c.dest.add " "

proc emit(c: var Context; token: string) =
  c.dest.add token

proc matchAndEmitTag(c: var Context; tag: TagId; asStr: string): bool =
  if c.current.kind == ParLe and c.current.tagId == tag:
    emit c, asStr
    inc c.current
    result = true
  else:
    result = false

proc nl(c: var Context) = c.dest.add "\n"

proc lookupSym(c: var Context): bool =
  if c.current.kind == Symbol:
    c.dest.add pool.syms[c.current.symId]
    inc c.current
    result = true
  else:
    result = false

proc declareSym(c: var Context): bool =
  if c.current.kind == Symbol:
    c.dest.add pool.syms[c.current.symId]
    inc c.current
    result = true
  else:
    result = false

template success(b: bool): bool = b

include asm_grammar

proc produceAsmCode*(buffer, outp: string) =
  #registerTags()
  var c = Context()
  setupInput c, buffer
  c.current = beginRead(c.input)
  if not genModule(c):
    error(c, "(stmts) expected")
  endRead(c.input, c.current)
  writeFile outp, c.dest
