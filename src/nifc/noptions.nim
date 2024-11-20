import std/[tables, assertions, syncio, os]
import cprelude

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

  Action* = enum
    atNone, atC, atCpp, atNative

  ConfigRef* {.acyclic.} = ref object ## every global configuration
    cCompiler*: SystemCC
    backend*: Backend
    options*: set[Option]
    optimizeLevel*: OptimizeLevel
    nifcacheDir*: string

  State* = object
    selects*: seq[string] # names of modules with functions with selectany pragmas
    config*: ConfigRef
    bits*: int

  ActionTable* = OrderedTable[Action, seq[string]]

proc initActionTable*(): ActionTable {.inline.} =
  result = initOrderedTable[Action, seq[string]]()

template getoptimizeLevelFlag*(config: ConfigRef): string =
  case config.optimizeLevel
  of Speed:
    "-O3"
  of Size:
    "-Os"
  of None:
    ""

template getCompilerConfig*(config: ConfigRef): (string, string) =
  case config.cCompiler
  of ccGcc:
    ("gcc", "g++")
  of ccCLang:
    ("clang", "clang++")
  else:
    quit "unreachable"

const ExtAction*: array[Action, string] = ["", ".c", ".cpp", ".S"]

proc genExcModule*(s: State, action: Action): string =
  assert action in {atC, atCpp}
  let suffix = ExtAction[action]
  result = "nifc_exc" & suffix
  var exc = open(s.config.nifcacheDir / result, fmWrite)
  exc.write "#define NIM_INTBITS " & $s.bits & "\n"
  exc.write Prelude
  exc.write "NB8 Err_;"
  exc.close()
