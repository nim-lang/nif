#
#
#           Gear3 Compiler
#        (c) Copyright 2024 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

##[

Gear 3
------

Gear 3 performs backend tasks that need to operate on multiple NIF files at once:

- It copies used imported symbols into the current NIF file. As a fix point operation
  until no foreign symbols are left.
- `importc`'ed symbols are replaced by their `.c` variants.
- `importc`'ed symbols might lead to `(incl "file.h")` injections.
- While it does that it performs proc inlining.
- Since it performs inlining it might as well also do iterator inlining
  so it does that too.


Grammar
-------

Gear 3 accepts Gear 2's grammar.

]##

import std / [parseopt, strutils, os, osproc, tables, assertions, syncio]
import expander

const
  Version = "0.2"
  Usage = "Gear3 Compiler. Version " & Version & """

  (c) 2024 Andreas Rumpf
Usage:
  gear3 [options] [command]
Command:
  file.nif      expand NIF file to meet NIFC's requirements

Options:
  --version                 show the version
  --help                    show this help
"""

proc writeHelp() = quit(Usage, QuitSuccess)
proc writeVersion() = quit(Version & "\n", QuitSuccess)

proc handleCmdLine() =
  var files: seq[string] = @[]
  for kind, key, val in getopt():
    case kind
    of cmdArgument:
      files.add key
    of cmdLongOption, cmdShortOption:
      case normalize(key)
      of "help", "h": writeHelp()
      of "version", "v": writeVersion()
      else: writeHelp()
    of cmdEnd: assert false, "cannot happen"
  if files.len > 1:
    quit "too many arguments given, seek --help"
  elif files.len == 0:
    writeHelp()
  else:
    expand files[0]

when isMainModule:
  handleCmdLine()
