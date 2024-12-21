#[

- Build the graph. Every node is a list of files representing the main source file plus its included files.
  - for this we also need the config so that the paths can be resolved properly
- Every node also has a list of dependencies. Every single dependency is a dependency to a modules's interface!

]#

import std/[os, tables, sets]
import semos, nifconfig, nimony_model
import ".." / gear2 / modnames

include nifprelude

type
  Node = ref object
    files: seq[string]
    deps: seq[string]

  DepContext = object
    config: NifConfig
    nodes: Table[string, Node]
    currentNode: Node
    includeStack: seq[string]
    processedModules: HashSet[string]

proc processDep(c: var DepContext; n: var Cursor)

proc processInclude(c: var DepContext; it: var Cursor) =
  var files: seq[string] = @[]
  var hasError = false
  let info = it.info
  var x = it
  skip it
  inc x # skip the `include`
  filenameVal(x, files, hasError)

  if hasError:
    discard "ignore wrong `include` statement"
  else:
    for f1 in items(files):
      let f2 = resolveFile(c.config.paths, getFile(info), f1)
      # check for recursive include files:
      var isRecursive = false
      for a in c.includeStack:
        if a == f2:
          isRecursive = true
          break

      if not isRecursive:
        c.currentNode.files.add f2
        var buf = parseFile(f2, c.config.paths)
        c.includeStack.add f2
        var n = cursorAt(buf, 0)
        processDep c, n
        c.includeStack.setLen c.includeStack.len - 1
      else:
        discard "ignore recursive include"

proc importSingleFile(c: var DepContext; f1, origin: string; info: PackedLineInfo) =
  let f2 = resolveFile(c.config.paths, origin, f1)
  let suffix = moduleSuffix(f2, c.config.paths)
  c.currentNode.deps.add f2
  if not c.processedModules.containsOrIncl(suffix):

    if needsRecompile(f2, suffix):
      selfExec c, f2

    loadInterface suffix, c.importTab

proc processImport(c: var DepContext; it: var Cursor) =
  let info = it.info
  var x = it
  skip it
  inc x # skip the `import`

  if x.kind == ParLe and x == "pragmax":
    inc x
    var y = x
    skip y
    if y.substructureKind == PragmasS:
      inc y
      if y.kind == Ident and pool.strings[y.litId] == "cyclic":
        return

  var files: seq[string] = @[]
  var hasError = false
  filenameVal(x, files, hasError)
  if hasError:
    discard "ignore wrong `import` statement"
  else:
    let origin = getFile(info)
    for f in files:
      importSingleFile c, f, origin, info

proc processDep(c: var DepContext; n: var Cursor) =
  case stmtKind(n)
  of ImportS:
    processImport c, n
  of IncludeS:
    processInclude c, n
  else:
    skip n

proc processDeps(config: sink NifConfig; n: Cursor) =
  var n = n
  var nested = 0
  var c = DepContext(config: config, currentNode: nil, includeStack: @[])
  while true:
    case n.kind
    of ParLe:
      inc nested
      if pool.tags[n.tagId] == "stmts":
        inc n
        processDep c, n

    of ParRi:
      dec nested
      inc n
    else: inc n
    if nested == 0: break

proc nimexec*(cmd: string) =
  let t = findExe("nim")
  if t.len == 0:
    quit("FAILURE: cannot find nim.exe / nim binary")
  exec quoteShell(t) & " " & cmd

proc requiresTool*(tool, src: string; forceRebuild: bool) =
  let t = findTool(tool)
  if not fileExists(t) or forceRebuild:
    nimexec("c -d:release " & src)
    moveFile src.changeFileExt(ExeExt), t

proc buildGraph(project: string) =
  var config = NifConfig()
  config.bits = sizeof(int)*8

  let nifler = findTool("nifler")
  let name = moduleSuffix(project, config.paths)
  let src = "nifcache" / name & ".1.nif"
  exec quoteShell(nifler) & " --portablePaths --deps parse " & quoteShell(project) & " " &
    quoteShell(src)

  let depsFile = src.changeFileExt(".deps.nif")
  var stream = nifstreams.open(depsFile)
  try:
    discard processDirectives(stream.r)
    var buf = fromStream(stream)
    processDeps config, beginRead buf
  finally:
    nifstreams.close(stream)


when isMainModule:
  createDir("nifcache")
  requiresTool "nifler", "src/nifler/nifler.nim", false

  buildGraph paramStr(1)
