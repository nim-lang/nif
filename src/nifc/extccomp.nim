import std/strutils
import noptions

type
  InfoCC* = tuple[
    name: string,        # the short name of the compiler
    optSpeed: string,    # the options for optimization for speed
    optSize: string,     # the options for optimization for size
    compilerExe: string, # the compiler's executable
    cppCompiler: string, # name of the C++ compiler's executable (if supported)
    ] # properties of the C compiler

# GNU C and C++ Compiler
const gcc: InfoCC = (
    name: "gcc",
    optSpeed: " -O3 -fno-ident",
    optSize: " -Os -fno-ident",
    compilerExe: "gcc",
    cppCompiler: "g++")

# Clang (LLVM) C/C++ Compiler
const clang: InfoCC = (
  name: "clang",
  optSpeed: " -O3 -fno-ident",
  optSize: " -Os -fno-ident",
  compilerExe: "clang",
  cppCompiler: "clang++"
)

const
  CC*: array[succ(low(SystemCC))..high(SystemCC), InfoCC] = [gcc, clang]

proc nameToCC*(name: string): SystemCC =
  ## Returns the kind of compiler referred to by `name`, or ccNone
  ## if the name doesn't refer to any known compiler.
  for i in succ(ccNone)..high(SystemCC):
    if cmpIgnoreStyle(name, CC[i].name) == 0:
      return i
  result = ccNone

proc listCCnames(): string =
  result = ""
  for i in succ(ccNone)..high(SystemCC):
    if i > succ(ccNone): result.add ", "
    result.add CC[i].name

proc setCC*(conf: ConfigRef; ccname: string) =
  conf.cCompiler = nameToCC(ccname)
  if conf.cCompiler == ccNone:
    quit "unknown C compiler: '$1'. Available options are: $2" % [ccname, listCCnames()]

proc getCompilerExe*(conf: ConfigRef; c: SystemCC): string =
  # TODO:
  result = CC[c].compilerExe

proc getCppCompiler*(conf: ConfigRef; c: SystemCC): string =
  # TODO:
  result = CC[c].cppCompiler

proc getOptSpeed*(conf: ConfigRef; c: SystemCC): string =
  # TODO:
  result = CC[c].optSpeed

proc getOptSize*(conf: ConfigRef; c: SystemCC): string =
  # TODO:
  result = CC[c].optSize
