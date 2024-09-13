#
#
#           NIFC Compiler
#        (c) Copyright 2024 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## NIFC driver program.

import std / [parseopt, strutils, os]
import codegen
import preasm / genpreasm

const
  Version = "0.2"
  Usage = "NIFC Compiler. Version " & Version & """

  (c) 2024 Andreas Rumpf
Usage:
  nifc [options] [command] [arguments]
Command:
  c|cpp|p file.nif [file2.nif]    convert NIF files to C|C++|PreASM

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
      else: writeHelp()
    of cmdEnd: assert false, "cannot happen"

  case action
  of "":
    writeHelp()
  of "c", "cpp":
    if args.len == 0:
      quit "command takes a filename"
    else:
      let destExt = if action == "c": ".c" else: ".cpp"
      var s = State()
      createDir("nifcache")
      for i in 0..<args.len:
        let inp = args[i]
        let outp = "nifcache" / splitFile(inp).name & destExt
        generateCode s, inp, outp, bits
      if s.selects.len > 0:
        var h = open("nifcache/select_any.h", fmWrite)
        for x in s.selects:
          write h, "#include \"" & extractFileName(x) & "\"\n"
        h.close()
  of "p":
    if args.len == 0:
      quit "command takes a filename"
    else:
      createDir("nifcache")
      for i in 0..<args.len:
        let inp = args[i]
        let outp = "nifcache" / splitFile(inp).name & ".preasm"
        generatePreAsm inp, outp, bits
  else:
    quit "Invalid action: " & action

when isMainModule:
  handleCmdLine()
