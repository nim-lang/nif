type
  Backend* = enum
    backendInvalid = "" # for parseEnum
    backendC = "c"
    backendCpp = "cpp"

  Option* = enum
    optOptimizeSpeed, optOptimizeSize

  SystemCC* = enum
    ccNone, ccGcc, ccNintendoSwitch, ccLLVM_Gcc, ccCLang, ccBcc, ccVcc,
    ccTcc, ccEnv, ccIcl, ccIcc, ccClangCl, ccHipcc, ccNvcc

  ConfigRef* {.acyclic.} = ref object ## every global configuration
    cCompiler*: SystemCC
    backend*: Backend
    options*: set[Option]

  State* = object
    selects*: seq[string] # names of modules with functions with selectany pragmas
    config*: ConfigRef
