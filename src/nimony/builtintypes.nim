#       Nimony
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

include nifprelude

type
  BuiltinTypes* = object
    mem: TokenBuf
    autoType*, stringType*, intType*, uintType*, floatType*, boolType*, charType*: Cursor
    voidType*, nilType*: Cursor

proc tagToken(tag: string; info: PackedLineInfo = NoLineInfo): PackedToken {.inline.} =
  toToken(ParLe, pool.tags.getOrIncl(tag), info)

proc createBuiltinTypes*(): BuiltinTypes =
  result = BuiltinTypes(mem: createTokenBuf(30))

  result.mem.add tagToken"auto" # 0
  result.mem.addParRi() # 1

  result.mem.add tagToken"string" # 2
  result.mem.addParRi() # 3

  result.mem.add tagToken"bool" # 4
  result.mem.addParRi() # 5

  let minusOne = pool.integers.getOrIncl(-1)
  result.mem.add tagToken"i" # 6
  result.mem.add toToken(IntLit, minusOne, NoLineInfo) # 7
  result.mem.addParRi() # 8

  result.mem.add tagToken"u" # 9
  result.mem.add toToken(IntLit, minusOne, NoLineInfo) # 10
  result.mem.addParRi() # 11

  result.mem.add tagToken"f" # 12
  result.mem.add toToken(IntLit, minusOne, NoLineInfo) # 13
  result.mem.addParRi() # 14

  result.mem.add tagToken"c" # 15
  result.mem.add toToken(IntLit, minusOne, NoLineInfo) # 16
  result.mem.addParRi() # 17

  result.mem.add toToken(DotToken, 0'u32, NoLineInfo) # 18

  result.mem.add tagToken"nilt" # 19
  result.mem.addParRi() # 20

  result.mem.freeze()

  result.autoType = result.mem.cursorAt(0)
  result.stringType = result.mem.cursorAt(2)
  result.boolType = result.mem.cursorAt(4)
  result.intType = result.mem.cursorAt(6)
  result.uintType = result.mem.cursorAt(9)
  result.floatType = result.mem.cursorAt(12)
  result.charType = result.mem.cursorAt(15)
  result.voidType = result.mem.cursorAt(18)
  result.nilType = result.mem.cursorAt(19)
