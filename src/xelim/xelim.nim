#
#
#           NIF Transformation
#        (c) Copyright 2024 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## xelim driver program.

import std / [parseopt, strutils, os]
import xelim_transformer

const
  Version = "0.2"
  Usage = "NIF xelim. Version " & Version & """

  (c) 2024 Andreas Rumpf
Usage:
  xelim [options] input.nif output.xelim.nif

eXpression elimination pass for NIF based compilers.

Options:
  --version             show the version
  --help                show this help
"""

proc writeHelp() = quit(Usage, QuitSuccess)
proc writeVersion() = quit(Version & "\n", QuitSuccess)

proc handleCmdLine() =
  var args: seq[string] = @[]
  for kind, key, val in getopt():
    case kind
    of cmdArgument:
      args.add key
    of cmdLongOption, cmdShortOption:
      case normalize(key)
      of "help", "h": writeHelp()
      of "version", "v": writeVersion()
      else: writeHelp()
    of cmdEnd: assert false, "cannot happen"

  if args.len == 1:
    args.add args[0].changeFileExt(".xelim.nif")
  if args.len < 2:
    quit "command takes two filenames"
  else:
    transformCode args[0], args[1]

when isMainModule:
  handleCmdLine()
