#       Nif library
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## A "program" is a set of NIF files.

import std / [tables, os]
import nifreader, generictrees, hybrids, lineinfos

type
  DefMode = enum
    Undef, Unfinished, FromFile, FromMem
  Definition = object
    m: DefMode
    n: LinkedNode
  Module = object
    r: Reader
  Program* = object
    modules: Table[string, Module]
    syms: Table[string, Definition]
    lits*: Literals
    code*: Tree # concat here so that NodePos always points into this seq.
    #dest: Tree
    thisModule: string
    nifdir: string

proc extractModuleSuffix(p: Program; name: string): string =
  var i = 0
  var c = 3
  while i < name.len:
    if name[i] == '.':
      dec c
      if c == 0:
        return name.substr(i+1)
    inc i
  return p.thisModule

proc fatal*(msg: string) =
  quit msg

proc loadModule(p: var Program; suffix: string) =
  if not p.modules.hasKey(suffix):
    let nifFile = p.nifdir / (suffix & ".nif")
    var r = nifreader.open(nifFile)
    if r.err:
      fatal "cannot open: " & nifFile
    r.trackDefs = true
    let res = processDirectives(r)
    if res != Success:
      fatal($res & " invalid file: " & nifFile)
    p.modules[suffix] = Module(r: r)

proc wasLoaded*(n: LinkedNode): bool {.inline.} =
  result = not n.isEmpty

proc loadSym*(p: var Program; name: string): LinkedNode =
  let d = p.syms.getOrDefault(name)
  if d.m == Undef:
    let suffix = extractModuleSuffix(p, name)
    if suffix == p.thisModule:
      # no attached reader!
      result = createEmpty()
    else:
      loadModule p, suffix
      let r = addr p.modules[suffix].r
      let rp = nifreader.jumpTo(r[], name)
      if success(rp):
        result = fromTreeAppend(p.code)
        discard parse(r[], p.code, p.lits, NoLineInfo)
        restore(r[], rp)
      else:
        result = createEmpty()
      p.syms[name] = Definition(m: FromFile, n: result)

proc loadHead*(p: var Program; name: string): LinkedNode =
  # The head of a symbol is its subtree up to but excluding the "body".
  # The body is what comes after "=":
  # proc p(args: int): returnType = ...
  # var x: int = ...
  result = loadSym(p, name)

proc loadBody*(p: var Program; name: string): LinkedNode =
  result = loadSym(p, name)
