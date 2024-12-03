

type
  int* {.magic: Int.}         ## Default integer type; bitwidth depends on
                              ## architecture, but is always the same as a pointer.
  float* {.magic: Float.}
  string* {.magic: String.}

  Color* = enum
    red = 0, blue = 1

  bool* {.magic: Bool.} = enum ## Built-in boolean type.
    false = 0, true = 1

proc `+`*(x, y: int): int {.magic: "AddI".}

proc foo(x: int; y: string): int =
  var x = "abc"
  result = 4

proc overloaded() =
  let someInt = `+`(23, 90)
  discard foo(34+56, "xyz")

proc overloaded(s: string) =
  discard "with string parameter"

type
  MyObject = object
    x, y: int

var global: MyObject

global.x = 45
discard foo(global.x, "123")

overloaded()
overloaded("abc")

proc discardable(x: int): int {.discardable.} =
  result = x + 7

discardable(123)
discard discardable(123)

proc foo_block* =
  var x = 12
  x = 3

  block lab:
    var s = 12
    break lab

  block:
    var s = 13
    break

  block lab:
    var s = 14
    break lab

  block late:
    block lab:
      var s = 12
      break lab
    block lab2:
      break late

proc testPragmaInline*() {.inline.} =
  let data = 1
