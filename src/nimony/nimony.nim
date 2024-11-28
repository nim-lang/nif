#       Nimony
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Nimony driver program.

import std / [parseopt, sets, strutils, os, assertions, syncio]

import ".." / gear3 / gear3 # only imported to ensure it keeps compiling
import ".." / gear2 / modnames
import sem, nifconfig

const
  Version = "0.2"
  Usage = "Nimony Compiler. Version " & Version & """

  (c) 2024 Andreas Rumpf
Usage:
  nimony [options] [command]
Command:
  m file.nim [project.nim]    compile a single Nim module to gear3

Options:
  -d, --define:SYMBOL       define a symbol for conditional compilation
  -p, --path:PATH           add PATH to the search path
  -r, --run                 run the makefile and the compiled program
  -f, --forcebuild          force a rebuild
  --noenv                   do not read configuration from `NIM_*`
                            environment variables
  --isSystem                passed module is a `system.nim` module
  --isMain                  passed module is the main module of a project
  --noSystem                do not auto-import `system.nim`
  --version                 show the version
  --help                    show this help
"""

proc writeHelp() = quit(Usage, QuitSuccess)
proc writeVersion() = quit(Version & "\n", QuitSuccess)

proc nimexec(cmd: string) =
  let t = findExe("nim")
  if t.len == 0:
    quit("FAILURE: cannot find nim.exe / nim binary")
  exec quoteShell(t) & " " & cmd

proc requiresTool(tool, src: string; forceRebuild: bool) =
  let t = findTool(tool)
  if not fileExists(t) or forceRebuild:
    nimexec("c -d:release " & src)
    moveFile src.changeFileExt(ExeExt), t

proc processSingleModule(nimFile: string; config: sink NifConfig; moduleFlags: set[ModuleFlag]) =
  let nifler = findTool("nifler")
  let name = moduleSuffix(nimFile)
  let src = "nifcache" / name & ".1.nif"
  let dest = "nifcache" / name & ".2.nif"
  exec quoteShell(nifler) & " --portablePaths p " & quoteShell(nimFile) & " " &
    quoteShell(src)
  if fileExists(src):
    semcheck(src, dest, ensureMove config, moduleFlags)

type
  Command = enum
    None, SingleModule

proc handleCmdLine() =
  var args: seq[string] = @[]
  var cmd = Command.None
  var forceRebuild = false
  var useEnv = true
  var moduleFlags: set[ModuleFlag] = {}
  var config = NifConfig()
  config.defines.incl "nimony"

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
      of "forcebuild", "f": forceRebuild = true
      of "path", "p": config.paths.add val
      of "define", "d": config.defines.incl val
      of "noenv": useEnv = false
      of "nosystem": moduleFlags.incl SkipSystem
      of "issystem": moduleFlags.incl IsSystem
      of "ismain": moduleFlags.incl IsMain
      else: writeHelp()
    of cmdEnd: assert false, "cannot happen"
  if args.len == 0:
    quit "too few command line arguments"
  elif args.len > 2:
    quit "too many command line arguments"
  if useEnv:
    let nimPath = getEnv("NIMPATH")
    for entry in split(nimPath, PathSep):
      if entry.strip != "":
        config.paths.add entry
  case cmd
  of None:
    quit "command missing"
  of SingleModule:
    createDir("nifcache")
    requiresTool "nifler", "src/nifler/nifler.nim", forceRebuild
    requiresTool "nifc", "src/nifc/nifc.nim", forceRebuild
    processSingleModule(args[0].addFileExt(".nim"), config, moduleFlags)

when isMainModule:
  handleCmdLine()
