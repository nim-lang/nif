
type
  int* {.magic: Int.}         ## Default integer type; bitwidth depends on
                              ## architecture, but is always the same as a pointer.
  float* {.magic: Float.}
  string* {.magic: String.}
  uint8* {.magic: UInt8.}

  set*[T] {.magic: Set.}
  array* [Index, T] {.magic: Array.}

var myset: set[uint8]
var myarr: array[3, int]
let u8 = 3'u8
myset = {1'u8, u8, 5'u8, 7'u8..9'u8}
myarr = [1, 2, 3]

type
  MyGeneric[T] = object
    x: T

var
  myglob: MyGeneric[int]
  other: MyGeneric[float]

myglob.x = 56
other.x = 79.0

proc `+`*(x, y: int): int {.magic: "AddI".}

template foobar() =
  break # allowed in a template

proc foo(x: int; y: string): int =
  var x = "abc"
  result = 4
  x = "34"

proc overloaded() =
  let someInt = `+`(23, 90)
  discard foo(34+56, "xyz")
