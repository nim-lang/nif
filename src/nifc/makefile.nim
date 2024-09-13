import std/[os, strformat]
import noptions

proc generateMakefile*(s: State, path: string; moduleNames: seq[string]; app: string; nifcache: string; compileOption: string) =
  var h = open(path, fmWrite)
  var makefileContent = "program:"
  var programBody = ""
  var objectBody = ""
  let cc =
    case s.config.backend
    of backendC:
      "$(CC)"
    of backendCpp:
      "$(CXX)"
    else:
      quit "unreachable"
  let cflags =
    case s.config.backend
    of backendC:
      "$(CFLAGS)"
    of backendCpp:
      "$(CXXFLAGS)"
    else:
      quit "unreachable"
  for i in 0..<moduleNames.len:
    makefileContent.add " " & moduleNames[i] & ".o"
    programBody.add " " & nifcache / moduleNames[i] & ".o"
    objectBody.add &"{moduleNames[i]}.o:\n	{cc} {cflags} -c " &
          nifcache / moduleNames[i] & ".c -o " &
          nifcache / moduleNames[i] & ".o\n"

  makefileContent.add &"\n	{cc} -o " & app & programBody & "\n\n" & objectBody

  h.write(makefileContent)
  h.close()
