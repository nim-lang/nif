
include std / prelude

type
  EntryKind = enum
    NodeKinds = "nodekinds"
    Magics = "magics"
    TypeFlags = "typeflags"
    SymFlags = "symflags"
    Options = "options"

  EntryOption = enum
    None, Ignore

  Entry = object
    k: EntryKind
    opt: EntryOption
    nim: string
    nif: string

proc processMap(f: string): seq[Entry] =
  var section = NodeKinds
  var counter = 0
  var dups = initHashSet[string]()
  result = @[]
  for line in lines(f):
    inc counter
    if line.len == 0: continue
    if line[0] == '#':
      section = parseEnum[EntryKind](line.substr(1).strip)
    else:
      let parts = line.split('|').mapIt(it.strip)
      if parts.len < 2:
        echo "illformed data at ", counter, ": ", line
      if dups.containsOrIncl(parts[1]):
        echo counter, " duplicated tag ", parts[1]

      let opt = if parts.len > 2 and parts[2] == "ignore": Ignore else: None
      result.add Entry(k: section, opt: opt, nim: parts[0], nif: parts[1])

proc genToNif(data: seq[Entry]) =
  discard

#--------------- to Nim --------------------------
#[

Idea: Generate this structure

proc nifToType(cache): PType = ...

proc nifToSym(cache): PSym = ...

proc nifToNode(cache, node): PNode =
  case node.kind
  of "addi":
    # call with magic
    n.sym = magicToSym()
    n.typ = n.sym.typ
  of "typeof":
    # prefer typeof node interpretation
  of "u":
    n.kind = nkType

]#

proc genToNim(data: seq[Entry]) =
  discard

let data = processMap "src/gear2/map.txt"
genToNif data
genToNim data
