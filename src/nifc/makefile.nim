import std/[os, strformat]

proc generateMakefile*(path: string; moduleNames: seq[string]; app: string; nifcache: string; compileOption: string) =
  var h = open(path, fmWrite)
  var makefileContent = "program:"
  var programBody = ""
  var objectBody = ""
  let cc = if compileOption == "c": "$(CC)" else: "$(CXX)"
  for i in 0..<moduleNames.len:
    makefileContent.add " " & moduleNames[i] & ".o"
    programBody.add " " & nifcache / moduleNames[i] & ".o"
    objectBody.add &"{moduleNames[i]}.o:\n	{cc} -c " &
          nifcache / moduleNames[i] & ".c -o " &
          nifcache / moduleNames[i] & ".o\n"

  makefileContent.add &"\n	{cc} -o " & app & programBody & "\n\n" & objectBody

  h.write(makefileContent)
  h.close() # TODO: exception?
