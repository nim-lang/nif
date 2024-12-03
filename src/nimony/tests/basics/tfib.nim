
type
  int* {.magic: Int.}
  bool* {.magic: Bool.}

proc `+`*(x, y: int): int {.magic: "AddI".}
proc `-`*(x, y: int): int {.magic: "SubI".}

proc `<=`*(x, y: int): bool {.magic: "LeI".}

proc fib[T](a: T): T =
  if a <= 2:
    result = 1
  else:
    result = fib(a-1) + fib(a-2)

discard fib(8)
