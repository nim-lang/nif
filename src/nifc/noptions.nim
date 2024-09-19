type
  Backend* = enum
    backendInvalid = "" # for parseEnum
    backendC = "c"
    backendCpp = "cpp"

  Option* = enum
    optLineDir

  OptimizeLevel* = enum
    None, Speed, Size

  SystemCC* = enum
    ccNone, ccGcc, ccCLang

  ConfigRef* {.acyclic.} = ref object ## every global configuration
    cCompiler*: SystemCC
    backend*: Backend
    options*: set[Option]
    optimizeLevel*: OptimizeLevel

  State* = object
    selects*: seq[string] # names of modules with functions with selectany pragmas
    config*: ConfigRef
