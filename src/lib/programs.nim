#       Nif library
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## A "program" is a set of NIF files.

import std / [tables, os]
import nifreader

type
  DefMode = enum
    Undef, Unfinished, FromFile, FromMem
  Definition = object
    m: DefMode
    n: RestorePoint
  Module = object
    r: Reader
  Program* = object
    modules: Table[string, Module]
    syms: Table[string, Definition]
    thisModule: string
    nifdir: string

proc extractModuleSuffix(p: Program; name: string): string =
  var i = name.len - 1
  while i >= 0:
    if name[i] == '.':
      return name.substr(i+1)
    dec i
  return p.thisModule

proc fatal*(msg: string) =
  quit msg

proc loadModule(p: var Program; suffix: string) =
  if not p.modules.hasKey(suffix):
    let nifFile = p.nifdir / (suffix & ".nif")
    var r = nifreader.open(nifFile)
    r.trackDefs = true
    let res = processDirectives(r)
    if res != Success:
      fatal($res & " invalid file: " & nifFile)
    p.modules[suffix] = Module(r: r)

proc wasLoaded*(n: RestorePoint): bool {.inline.} =
  result = n.success

proc loadSym*(p: var Program; name: string): RestorePoint =
  let d = p.syms.getOrDefault(name)
  if d.m == Undef:
    let suffix = extractModuleSuffix(p, name)
    if suffix == p.thisModule:
      # no attached reader!
      result = default(RestorePoint)
    else:
      loadModule p, suffix
      let r = addr p.modules[suffix].r
      let old = savePos(r[])
      let rp = nifreader.jumpTo(r[], name)
      if success(rp):
        result = rp
        restore(r[], old)
      else:
        result = default(RestorePoint)
      p.syms[name] = Definition(m: FromFile, n: result)
