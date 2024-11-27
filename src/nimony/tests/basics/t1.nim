

type
  int* {.magic: Int.}         ## Default integer type; bitwidth depends on
                              ## architecture, but is always the same as a pointer.
  float* {.magic: Float.}
  string* {.magic: String.}


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
