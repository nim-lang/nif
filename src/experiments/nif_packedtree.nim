#       Nif library
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Parse NIF into a packed tree representation.

import bitabs, lineinfos, stringviews, packedtrees, nifreader

type
  NifKind* = enum
    Empty, Ident, Sym, Symdef, IntLit, UIntLit, FloatLit, CharLit, StrLit,
    Err, # must not be an atom!
    Compound

type
  StrId* = distinct uint32
  IntId* = distinct uint32
  UIntId* = distinct uint32
  FloatId* = distinct uint32
  KindId* = distinct uint32
  Literals* = object
    man*: LineInfoManager
    kinds*: BiTable[KindId, string]
    files*: BiTable[FileId, string] # we cannot use StringView here as it may have unexpanded backslashes!
    strings*: BiTable[StrId, string]
    integers*: BiTable[IntId, int64]
    uintegers*: BiTable[UIntId, uint64]
    floats*: BiTable[FloatId, float64]

proc addAtom*[L](dest: var PackedTree[NifKind]; kind: NifKind; lit: L; info: PackedLineInfo) =
  packedtrees.addAtom dest, kind, uint32(lit), info

proc parse*(r: var Reader; dest: var PackedTree[NifKind]; lits: var Literals; parentInfo: PackedLineInfo): bool =
  let t = next(r)
  var currentInfo = parentInfo
  if t.filename.len == 0:
    # relative file position
    if t.pos.line != 0 or t.pos.col != 0:
      let (file, line, col) = unpack(lits.man, parentInfo)
      currentInfo = pack(lits.man, file, line+t.pos.line, col+t.pos.col)
  else:
    # absolute file position:
    let fileId = lits.files.getOrIncl(decodeFilename t)
    currentInfo = pack(lits.man, fileId, t.pos.line, t.pos.col)

  result = true
  case t.tk
  of EofToken, ParRi:
    result = false
  of ParLe:
    #let kind = whichKind(t.s, Err)
    let ka = lits.kinds.getOrInclFromView(t.s).uint32 + ord(Compound).uint32
    let kb = if ka > 255'u32: ord(Compound).uint32 else: ka
    copyInto(dest, cast[NifKind](kb), currentInfo):
      if ka > 255'u32:
        # handle overflow:
        dest.addAtom Ident, ka, currentInfo
      while true:
        let progress = parse(r, dest, lits, currentInfo)
        if not progress: break

  of UnknownToken:
    copyInto dest, Err, currentInfo:
      dest.addAtom StrLit, lits.strings.getOrIncl(decodeStr t), currentInfo
  of DotToken:
    dest.addAtom Empty, 0'u32, currentInfo
  of Ident:
    dest.addAtom Ident, lits.strings.getOrIncl(decodeStr t), currentInfo
  of Symbol:
    dest.addAtom Sym, lits.strings.getOrIncl(decodeStr t), currentInfo
  of SymbolDef:
    dest.addAtom Symdef, lits.strings.getOrIncl(decodeStr t), currentInfo
  of StringLit:
    dest.addAtom StrLit, lits.strings.getOrIncl(decodeStr t), currentInfo
    # XXX handle suffixes
  of CharLit:
    dest.addAtom CharLit, uint32 decodeChar(t), currentInfo
  of IntLit:
    dest.addAtom IntLit, lits.integers.getOrIncl(decodeInt t), currentInfo
    # XXX handle suffixes
  of UIntLit:
    dest.addAtom UIntLit, lits.uintegers.getOrIncl(decodeUInt t), currentInfo
    # XXX handle suffixes
  of FloatLit:
    dest.addAtom FloatLit, lits.floats.getOrIncl(decodeFloat t), currentInfo
    # XXX handle suffixes

type
  Module* = object
    t*: PackedTree[NifKind]
    lits*: Literals

proc parse*(r: var Reader): Module =
  # empirically, (size div 7) is a good estimate for the number of nodes
  # in the file:
  result = Module(t: createPackedTree[NifKind](r.fileSize div 7))
  discard parse(r, result.t, result.lits, NoLineInfo)

proc memSizes*(m: Module) =
  echo "Tree ", m.t.len # * sizeof(PackedNode[NifKind])
  echo "Man ", m.lits.man.memSize
  echo "Kinds ", m.lits.kinds.memSize
  echo "Files ", m.lits.files.memSize
  echo "Strings ", m.lits.strings.memSize
  echo "Ints ", m.lits.integers.memSize
  echo "UInts ", m.lits.uintegers.memSize
  echo "Floats ", m.lits.floats.memSize
