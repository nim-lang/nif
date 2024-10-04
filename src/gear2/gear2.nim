when not defined(nimcore):
  {.error: "nimcore MUST be defined for Nim's core tooling".}

import std / [os, times, parseopt]
import "$nim" / compiler / [
  ast, options, msgs, condsyms, idents, platform,
  modules, pipelines, packages, modulegraphs, lineinfos, pathutils,
  cmdlinehelper, commands]

when defined(loadFromNif):
  # XXX Enable once NIF generation works
  proc importPipelineModule2(graph: ModuleGraph; s: PSym, fileIdx: FileIndex): PSym =
    # this is called by the semantic checking phase
    assert graph.config != nil
    result = nil # to implement

  proc connectPipelineCallbacks2(graph: ModuleGraph) =
    graph.includeFileCallback = modules.includeModule
    graph.importModuleCallback = importPipelineModule2

  proc compilePipelineSystemModule2(graph: ModuleGraph) =
    if graph.systemModule == nil:
      connectPipelineCallbacks2(graph)
      graph.config.m.systemFileIdx = fileInfoIdx(graph.config,
          graph.config.libpath / RelativeFile"system.nim")
      discard graph.compilePipelineModule(graph.config.m.systemFileIdx, {sfSystemModule})

  proc compilePipelineProject*(graph: ModuleGraph; projectFileIdx = InvalidFileIdx) =
    connectPipelineCallbacks2(graph)
    let conf = graph.config
    wantMainModule(conf)
    configComplete(graph)

    let systemFileIdx = fileInfoIdx(conf, conf.libpath / RelativeFile"system.nim")
    let projectFile = if projectFileIdx == InvalidFileIdx: conf.projectMainIdx else: projectFileIdx
    conf.projectMainIdx2 = projectFile

    let packSym = getPackage(graph, projectFile)
    graph.config.mainPackageId = packSym.getPackageId
    graph.importStack.add projectFile

    if projectFile == systemFileIdx:
      discard graph.compilePipelineModule(projectFile, {sfMainModule, sfSystemModule})
    else:
      graph.compilePipelineSystemModule2()
      discard graph.compilePipelineModule(projectFile, {sfMainModule})

proc commandCheck(graph: ModuleGraph) =
  let conf = graph.config
  conf.setErrorMaxHighMaybe
  defineSymbol(conf.symbols, "nimcheck")
  if optWasNimscript in conf.globalOptions:
    defineSymbol(conf.symbols, "nimscript")
    defineSymbol(conf.symbols, "nimconfig")
  elif conf.backend == backendJs:
    setTarget(conf.target, osJS, cpuJS)
  setPipeLinePass(graph, SemPass)
  compilePipelineProject(graph)

proc processCmdLine(pass: TCmdLinePass, cmd: string; config: ConfigRef) =
  var p = parseopt.initOptParser(cmd)
  var argsCount = 0

  config.commandLine.setLen 0
    # bugfix: otherwise, config.commandLine ends up duplicated

  while true:
    parseopt.next(p)
    case p.kind
    of cmdEnd: break
    of cmdLongOption, cmdShortOption:
      config.commandLine.add " "
      config.commandLine.addCmdPrefix p.kind
      config.commandLine.add p.key.quoteShell # quoteShell to be future proof
      if p.val.len > 0:
        config.commandLine.add ':'
        config.commandLine.add p.val.quoteShell

      if p.key == "": # `-` was passed to indicate main project is stdin
        p.key = "-"
        if processArgument(pass, p, argsCount, config): break
      else:
        processSwitch(pass, p, config)
    of cmdArgument:
      config.commandLine.add " "
      config.commandLine.add p.key.quoteShell
      if processArgument(pass, p, argsCount, config): break
  if pass == passCmd2:
    if {optRun, optWasNimscript} * config.globalOptions == {} and
        config.arguments.len > 0 and config.cmd notin {cmdTcc, cmdNimscript, cmdCrun}:
      rawMessage(config, errGenerated, errArgsNeedRunOption)

proc mainCommand(graph: ModuleGraph) =
  let conf = graph.config
  conf.lastCmdTime = epochTime()
  conf.searchPaths.add(conf.libpath)
  if conf.cmd == cmdM:
    commandCheck graph
  else:
    rawMessage conf, errGenerated, "only the 'm' command is supported for now"

proc handleCmdLine(cache: IdentCache; conf: ConfigRef) =
  let self = NimProg(
    supportsStdinFile: true,
    processCmdLine: processCmdLine
  )
  self.initDefinesProg(conf, "nim_compiler")
  if paramCount() == 0:
    writeCommandLineUsage(conf)
    return

  self.processCmdLineAndProjectPath(conf)

  var graph = newModuleGraph(cache, conf)
  if not self.loadConfigsAndProcessCmdLine(cache, conf, graph):
    return

  if conf.cmd == cmdCheck and optWasNimscript notin conf.globalOptions and
       conf.backend == backendInvalid:
    conf.backend = backendC

  if conf.selectedGC == gcUnselected:
    if conf.backend in {backendC, backendCpp, backendObjc} or
        (conf.cmd in cmdDocLike and conf.backend != backendJs) or
        conf.cmd == cmdGendepend:
      initOrcDefines(conf)

  mainCommand(graph)

when isMainModule:
  handleCmdLine(newIdentCache(), newConfigRef())
