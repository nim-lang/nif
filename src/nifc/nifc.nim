#
#
#           NIFC Compiler
#        (c) Copyright 2024 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## NIFC driver program.

import std / [parseopt, strutils, os, osproc]
import codegen, makefile, noptions
import preasm / genpreasm

when defined(enableAsm):
  import amd64 / genasm

const
  Version = "0.2"
  Usage = "NIFC Compiler. Version " & Version & """

  (c) 2024 Andreas Rumpf
Usage:
  nifc [options] [command] [arguments]
Command:
  c|cpp|p file.nif [file2.nif]    convert NIF files to C|C++|PreASM

Options:
  -r, --run                 run the makefile and the compiled program
  --cc:SYMBOL               specify the C compiler
  --opt:none|speed|size     optimize not at all or for speed|size
  --lineDir:on|off          generation of #line directive on|off
  --bits:N                  (int M) has N bits; possible values: 64, 32, 16
  --version                 show the version
  --help                    show this help
"""

proc writeHelp() = quit(Usage, QuitSuccess)
proc writeVersion() = quit(Version & "\n", QuitSuccess)

proc genMakeCmd(config: ConfigRef, makefilePath: string): string =
  let optimizeLevelFlag = case config.optimizeLevel
    of Speed:
      "-O3"
    of Size:
      "-Os"
    of None:
      ""

  let (cCompiler, cppCompiler) =
    case config.cCompiler
    of ccGcc:
      ("gcc", "g++")
    of ccCLang:
      ("clang", "clang++")
    else:
      quit "unreachable"

  result = case config.backend
    of backendC:
      "make " & "CC=" & cCompiler &
          " " & "CFLAGS=" & "\"" & optimizeLevelFlag & "\"" &
          " -f " & makefilePath
    of backendCpp:
      "make " & "CXX=" & cppCompiler &
          " " & "CXXFLAGS=" & "\"" & optimizeLevelFlag & "\"" &
          " -f " & makefilePath
    else:
      quit "unreachable"

proc handleCmdLine() =
  var action = ""
  var args: seq[string] = @[]
  var bits = sizeof(int)*8
  var toRun = false


  var s = State(config: ConfigRef())
  when defined(macos): # TODO: switches to default config for platforms
    s.config.cCompiler = ccCLang
  else:
    s.config.cCompiler = ccGcc
  for kind, key, val in getopt():
    case kind
    of cmdArgument:
      if action.len == 0:
        action = key.normalize
      else:
        args.add key
    of cmdLongOption, cmdShortOption:
      case normalize(key)
      of "bits":
        case val
        of "64": bits = 64
        of "32": bits = 32
        of "16": bits = 16
        else: quit "invalid value for --bits"
      of "help", "h": writeHelp()
      of "version", "v": writeVersion()
      of "run", "r": toRun = true
      of "cc":
        case val.normalize
        of "gcc":
          s.config.cCompiler = ccGcc
        of "clang":
          s.config.cCompiler = ccCLang
        else:
          quit "unknown C compiler: '$1'. Available options are: gcc, clang" % [val]
      of "opt":
        case val.normalize
        of "speed":
          s.config.optimizeLevel = Speed
        of "size":
          s.config.optimizeLevel = Size
        of "none":
          s.config.optimizeLevel = None
        else:
          quit "'none', 'speed' or 'size' expected, but '$1' found" % val
      of "linedir":
        case val.normalize
        of "", "on":
          s.config.options.incl optLineDir
        of "off":
          s.config.options.excl optLineDir
        else:
          quit "'on', 'off' expected, but '$1' found" % val
      else: writeHelp()
    of cmdEnd: assert false, "cannot happen"

  case action
  of "":
    writeHelp()
  of "c", "cpp":
    if args.len == 0:
      quit "command takes a filename"
    else:
      s.config.backend = if action == "c": backendC else: backendCpp
      let destExt = if action == "c": ".c" else: ".cpp"
      var moduleNames = newSeq[string](args.len)
      let nifcacheDir = "nifcache"
      createDir(nifcacheDir)
      for i in 0..<args.len:
        let inp = args[i]
        moduleNames[i] = splitFile(inp).name
        let outp = nifcacheDir / moduleNames[i] & destExt
        generateCode s, inp, outp, bits
      if s.selects.len > 0:
        var h = open(nifcacheDir / "select_any.h", fmWrite)
        for x in s.selects:
          write h, "#include \"" & extractFileName(x) & "\"\n"
        h.close()
      let appName = moduleNames[^1]
      let makefilePath = nifcacheDir / "Makefile." & appName
      generateMakefile(s, makefilePath, moduleNames, appName, nifcacheDir, action, destExt)
      if toRun:
        let makeCmd = genMakeCmd(s.config, makefilePath)
        let (output, exitCode) = execCmdEx(makeCmd)
        if exitCode != 0:
          quit "execution of an external program failed: " & output
        if execCmd("./" & appName) != 0:
          quit "execution of an external program failed: " & appName
  of "p":
    if args.len == 0:
      quit "command takes a filename"
    else:
      for inp in items args:
        let outp = changeFileExt(inp, ".preasm")
        generatePreAsm inp, outp, bits
  of "asm":
    if args.len == 0:
      quit "command takes a filename"
    else:
      when defined(enableAsm):
        for inp in items args:
          let outp = changeFileExt(inp, ".asm")
          generateAsm inp, outp
      else:
        quit "wasn't built with native target support"
  else:
    quit "Invalid action: " & action

when isMainModule:
  handleCmdLine()
