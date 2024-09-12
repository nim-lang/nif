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

const
  Version = "0.2"
  Usage = "NIFC Compiler. Version " & Version & """

  (c) 2024 Andreas Rumpf
Usage:
  nifc [options] [command] [arguments]
Command:
  c|cpp file.nif [file2.nif]    convert NIF files to C|C++

Options:
  --bits:N              (int M) has N bits; possible values: 64, 32, 16
  --version             show the version
  --help                show this help
"""

proc writeHelp() = quit(Usage, QuitSuccess)
proc writeVersion() = quit(Version & "\n", QuitSuccess)

proc handleCmdLine() =
  var action = ""
  var args: seq[string] = @[]
  var bits = sizeof(int)*8
  var toRun = false

  var ccOption = ""
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
      of "cc": ccOption = val
      else: writeHelp()
    of cmdEnd: assert false, "cannot happen"

  case action
  of "":
    writeHelp()
  of "c", "cpp":
    if args.len == 0:
      quit "command takes a filename"
    else:
      var s = State(backend: if action == "c": backendC else: backendCpp)
      let destExt = if action == "c": ".c" else: ".cpp"
      when defined(windows):
        case s.backend
        of backendC:
          ccOption = "gcc"
        of backendCpp:
          ccOption = "g++"
        else:
          quit "unreachable"
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
      generateMakefile(s, makefilePath, moduleNames, appName, nifcacheDir, action)
      if toRun:
        let ccIdent =  case s.backend
          of backendC:
            "CC"
          of backendCpp:
            "CXX"
          else:
            quit "unreachable"

        let makeCmd =
          if ccOption.len > 0: "make " & ccIdent & "=" & ccOption & " -f " & makefilePath
          else: "make -f " & makefilePath
        let (output, exitCode) = execCmdEx(makeCmd)
        if exitCode != 0:
          quit "execution of an external program failed: " & output
        if execCmd("./" & appName) != 0:
          quit "execution of an external program failed: " & appName
  else:
    quit "Invalid action: " & action

when isMainModule:
  handleCmdLine()
