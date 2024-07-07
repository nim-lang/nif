#       Nifler
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Nifler is a simple tool that parses Nim code and outputs NIF code.
## No semantic checking is done and no symbol lookups are performed.

import std / [parseopt, strutils, os]
import emitter, bridge

const
  Version = "0.2"
  Usage = "Nifler - Tools related to NIF. Version " & Version & """

  (c) 2024 Andreas Rumpf
Usage:
  nifler [options] [command] [arguments]
Command:
  p|parse file.nim [output.nif]     parse project.nim and produce a NIF file

Options:
  --version             show the version
  --help                show this help
"""

proc writeHelp() = quit(Usage, QuitSuccess)
proc writeVersion() = quit(Version & "\n", QuitSuccess)

proc main(infile, outfile: string) =
  var em = Emitter(minified: true)
  parseFile em, infile
  if em.output.len > 0:
    writeFile outfile, em.output

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
  of "p", "parse":
    if args.len == 0:
      quit "'parse' command takes a filename"
    else:
      let inp = args[0]
      let outp = if args.len >= 2: args[1].addFileExt".nif" else: changeFileExt(inp, ".nif")
      main inp, outp
  else:
    quit "Invalid action: " & action

when isMainModule:
  handleCmdLine()
