
include std / prelude

type
  EntryKind = enum
    NodeKinds = "TNodeKind"
    Magics = "TMagic"
    TypeFlags = "TTypeFlags"
    SymFlags = "TSymFlags"
    Options = "TOptions"
    TypeKinds = "TTypeKind"
  EntryType = enum
    IsEnum = "enum"
    IsSet = "set"

  EntryOption = enum
    None,
    Ignore = "ignore",
    GenericHead = "genericHead",
    Sym = "sym",
    last,
    skipModifier,
    withnode
    override
    typekind
    symkind
    nodekind

  Entry = object
    k: EntryKind
    t: EntryType
    opt: EntryOption
    nim: string
    nif: string

proc processMap(f: string): seq[Entry] =
  var section = NodeKinds
  var t = IsEnum
  var counter = 0
  var dups = initHashSet[string]()
  result = @[]
  for line in lines(f):
    inc counter
    if line.len == 0: continue
    let parts = line.split('|').mapIt(it.strip)
    if parts.len < 2:
      echo "illformed data at ", counter, ": ", line
    elif line[0] == '#':
      section = parseEnum[EntryKind](parts[0].substr(1).strip)
      t = parseEnum[EntryType](parts[1])
    else:
      if dups.containsOrIncl(parts[1]):
        echo counter, " duplicated tag ", parts[1]
      let opt = if parts.len > 2: parseEnum[EntryOption](parts[2]) else: None
      result.add Entry(k: section, t: t, opt: opt, nim: parts[0], nif: parts[1])

proc addv(s: var string; args: varargs[string]) =
  for a in args: s.add a

proc conc(args: varargs[string]): string =
  result = ""
  for a in args: result.add a

proc cleanNameL(s: string): string =
  result = $toLowerAscii(s[1])
  for i in 2 ..< s.len: result.add s[i]

proc shouldIgnore(opt: EntryOption): bool = opt in {Ignore, typekind, symkind}

proc genToNif(f: var File; data: seq[Entry]) =
  var a = default array[EntryKind, string]
  var cases = default array[EntryKind, HashSet[string]]
  for d in data:
    if d.opt.shouldIgnore: continue
    case d.t
    of IsEnum:
      if a[d.k].len == 0:
        a[d.k] = conc("proc ", cleanNameL($d.k), "ToTag*(k: ", $d.k, "): string = ",
          "\n  case k")
      if not cases[d.k].containsOrIncl(d.nim):
        a[d.k].addv "\n  of ", d.nim, ": ", escape(d.nif)
    of IsSet:
      if a[d.k].len == 0:
        a[d.k] = conc("proc ", cleanNameL($d.k), "ToKeyw*(f: ", $d.k, "; b: var Builder) = ")
      a[d.k].addv "\n  if ", d.nim, " in f: b.addKeyw ", escape(d.nif)
  for x in a:
    f.writeLine("")
    f.writeLine(x)

proc cleanNameU(s: string): string =
  result = $toUpperAscii(s[1])
  for i in 2 ..< s.len: result.add s[i]

proc genToNim(f: var File; data: seq[Entry]) =
  var a = default array[EntryKind, string]
  var cases = default array[EntryKind, HashSet[string]]
  for d in data:
    if d.opt.shouldIgnore: continue
    case d.t
    of IsEnum:
      if not cases[d.k].containsOrIncl(d.nif):
        if a[d.k].len == 0:
          a[d.k] = conc("proc to", cleanNameU($d.k), "*(tag: string): ", $d.k, " = ",
            "\n  case tag")
        let x = d.nim.split(',')
        let n = if x.len > 0: x[0] else: d.nim
        a[d.k].addv "\n  of ", escape(d.nif), ": ", n
    of IsSet:
      #let e = ($d.k)[0..^2]
      if a[d.k].len == 0:
        a[d.k] = conc("proc incl", cleanNameU($d.k), "*(res: var ", $d.k, "; f: string) = ",
          "\n  case f")
      a[d.k].addv "\n  of ", escape(d.nif) , ": res.incl ", d.nim

  var endingsGenerated = initHashSet[string]()
  for d in data:
    if d.opt.shouldIgnore: continue
    case d.t
    of IsEnum:
      if a[d.k].len > 0:
        if not endingsGenerated.containsOrIncl($d.k):
          a[d.k].addv "\n  else: low ", $d.k

    of IsSet: discard

  for x in a:
    f.writeLine("")
    f.writeLine(x)

proc generate =
  let data = processMap "src/gear2/generator/map.txt"
  var f = open("src/gear2/tags.nim", fmWrite)
  f.writeLine("# Generated by mapping.nim: DO NOT EDIT!")
  genToNif f, data
  genToNim f, data

generate()
