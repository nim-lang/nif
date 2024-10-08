import std/[os, strformat, tables, syncio]
import noptions

proc generateMakefileForFiles(s: State, files: seq[string],
      makefileContent: var string, programBody: var string,
      objectBody: var string,
      cc: string, cflags: string, destExt: string
    ) =
  let nifcacheDir = s.config.nifcacheDir
  for i in 0..<files.len:
    let moduleNames = splitFile(files[i]).name
    makefileContent.add " " & moduleNames & ".o"
    programBody.add " " & nifcacheDir / moduleNames & ".o"
    objectBody.add &"{moduleNames}.o:\n	{cc} {cflags} -c " &
          nifcacheDir / moduleNames & fmt"{destExt} -o " &
          nifcacheDir / moduleNames & ".o\n"

proc generateMakefileForAsm(s: State, files: seq[string],
      makefileContent: var string, programBody: var string,
      objectBody: var string,
      ccLinker: string) =
  let nifcacheDir = s.config.nifcacheDir
  const destExt = ".S"
  for i in 0..<files.len:
    let moduleNames = splitFile(files[i]).name
    makefileContent.add " " & moduleNames & ".o"
    programBody.add " " & nifcacheDir / moduleNames & ".o"
    objectBody.add &"{moduleNames}.o:\n	{ccLinker} -c " &
          nifcacheDir / moduleNames & fmt"{destExt} -o " &
          nifcacheDir / moduleNames & ".o\n"

proc generateMakefile*(s: State, path: string; app: string; actionTable: ActionTable) =
  var h = open(path, fmWrite)
  var makefileContent = "program:"
  var programBody = ""
  var objectBody = ""

  let ccLinker = if atCpp in actionTable: "$(CXX)" else: "$(CC)"
  for action in actionTable.keys:
    case action
    of atC, atCpp:
      let (cc, cflags, destExt) = case action
        of atC:
          ("$(CC)", "$(CFLAGS)", ".c")
        of atCpp:
          ("$(CXX)", "$(CXXFLAGS)", ".cpp")
        else:
          quit "unreachable"
      generateMakefileForFiles(s, actionTable[action],
          makefileContent, programBody, objectBody,
          cc, cflags, destExt)
    of atNative:
      generateMakefileForAsm(s, actionTable[action],
          makefileContent, programBody, objectBody, ccLinker)
    else:
      quit "unreachable"

  makefileContent.add &"\n	{ccLinker} -o " & app & programBody & "\n\n" & objectBody

  h.write(makefileContent)
  h.close()
