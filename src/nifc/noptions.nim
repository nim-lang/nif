type
  Backend* = enum
    backendInvalid = "" # for parseEnum
    backendC = "c"
    backendCpp = "cpp"

  State* = object
    selects*: seq[string] # names of modules with functions with selectany pragmas
    backend*: Backend
