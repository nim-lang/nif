#       Nimony
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Nimony driver program.

import std / [parseopt, strutils, os, assertions, syncio]

const
  Version = "0.2"
  Usage = "Nimony Compiler. Version " & Version & """

  (c) 2024 Andreas Rumpf
Usage:
  nimony [options] [command]
Command:
  m file.nim [project.nim]    compile a single Nim module to gear3

Options:
  -r, --run                 run the makefile and the compiled program
  --version                 show the version
  --help                    show this help
"""

proc writeHelp() = quit(Usage, QuitSuccess)
proc writeVersion() = quit(Version & "\n", QuitSuccess)

type
  Command = enum
    None, SingleModule

proc handleCmdLine() =
  var args: seq[string] = @[]
  var cmd = Command.None

  for kind, key, val in getopt():
    case kind
    of cmdArgument:
      if cmd == None:
        case key.normalize:
        of "m":
          cmd = SingleModule
        else:
          quit "command expected"
      else:
        args.add key

    of cmdLongOption, cmdShortOption:
      case normalize(key)
      of "help", "h": writeHelp()
      of "version", "v": writeVersion()
      else: writeHelp()
    of cmdEnd: assert false, "cannot happen"
  if args.len == 0:
    quit "too few command line arguments"
  elif args.len > 2:
    quit "too many command line arguments"
  createDir("nifcache")

when isMainModule:
  handleCmdLine()
