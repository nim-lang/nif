type
  bool* {.magic: Bool.} = enum ## Built-in boolean type.
    false = 0, true = 1

when true:
  discard "good"
else:
  discard "bad"

when false:
  discard "bad"
else:
  discard "good"

const isMainModule* {.magic: IsMainModule.} = false

when isMainModule:
  discard "good"
else:
  discard "bad"

when false:
  proc defined*(x: untyped): bool {.magic: Defined.}

  when defined(nimony):
    discard "good"
  else:
    discard "bad"

  when defined(undefinedDefine):
    discard "bad"
  else:
    discard "good"

  when defined(nimony) and not defined(undefinedDefine):
    discard "good"
  else:
    discard "bad"

  when defined(undefinedDefine) or not defined(nimony):
    discard "bad"
  else:
    discard "good"
