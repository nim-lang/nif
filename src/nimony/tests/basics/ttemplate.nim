
type
  int* {.magic: Int.}         ## Default integer type; bitwidth depends on
                              ## architecture, but is always the same as a pointer.
  float* {.magic: Float.}
  string* {.magic: String.}

  array* [Index, T] {.magic: Array.}

type
  MyGeneric[T] = object
    x: T

var
  myglob: MyGeneric[int]
  other: MyGeneric[float]

myglob.x = 56
other.x = 79.0

proc `+`*(x, y: int): int {.magic: "AddI".}

template plus(x, y: int): int = x + y

proc foo(x: int; y: string): int =
  var x = "abc"
  result = plus(4, plus(2, 89))
  x = "34"

proc overloaded() =
  let someInt = `+`(23, 90)
  discard foo(34+56, "xyz")
