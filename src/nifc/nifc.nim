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

const
  Version = "0.2"
  Usage = "NIFC Compiler. Version " & Version & """

  (c) 2024 Andreas Rumpf
Usage:
  nifler [options] [command] [arguments]
Command:
  c|cpp file.nif [output.c]     convert the NIF file to C|C++

Options:
  --version             show the version
  --help                show this help
"""

proc writeHelp() = quit(Usage, QuitSuccess)
proc writeVersion() = quit(Version & "\n", QuitSuccess)

proc handleCmdLine() =
  var action = ""
  var args: seq[string] = @[]
  for kind, key, val in getopt():
    case kind
    of cmdArgument:
      if action.len == 0:
        action = key.normalize
      else:
        args.add key
    of cmdLongOption, cmdShortOption:
      case normalize(key)
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
      let inp = args[0]
      let outp = if args.len >= 2: args[1].addFileExt(destExt) else: changeFileExt(inp, destExt)
      generateCode inp, outp
  else:
    quit "Invalid action: " & action

when isMainModule:
  handleCmdLine()
