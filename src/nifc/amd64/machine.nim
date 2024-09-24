#
#
#           NIFC Compiler
#        (c) Copyright 2024 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

import ".." / nifc_model
import ".." / native / slots

import nifstreams except StrId

type
  IntReg* = distinct byte
  FloatReg* = distinct byte
  CpuFlag* = distinct byte

proc inc(x: var IntReg) {.inline.} = inc byte(x)
proc inc(x: var FloatReg) {.inline.} = inc byte(x)

proc `==`*(a, b: IntReg): bool {.borrow.}
proc `<=`(a, b: IntReg): bool {.borrow.}
proc `<`(a, b: IntReg): bool {.borrow.}

proc `==`*(a, b: FloatReg): bool {.borrow.}
proc `<=`(a, b: FloatReg): bool {.borrow.}
proc `<`(a, b: FloatReg): bool {.borrow.}

proc `==`*(a, b: CpuFlag): bool {.borrow.}
proc `<=`(a, b: CpuFlag): bool {.borrow.}
proc `<`(a, b: CpuFlag): bool {.borrow.}

const
  Rax = IntReg(0)
  Rbx = IntReg(1)
  Rcx* = IntReg(2)
  Rdx = IntReg(3)
  Rsi = IntReg(4)
  Rdi = IntReg(5)
  Rbp = IntReg(6)
  Rsp* = IntReg(7)
  R8 = IntReg(8)
  R9 = IntReg(9)
  R10 = IntReg(10)
  R11 = IntReg(11)
  R12 = IntReg(12)
  R13 = IntReg(13)
  R14 = IntReg(14)
  R15 = IntReg(15)

  LastIntReg = R15

proc regName*(r: IntReg): string =
  case r
  of Rax: result = "RAX"
  of Rbx: result = "RBX"
  of Rcx: result = "RCX"
  of Rdx: result = "RDX"
  of Rsi: result = "RCX"
  of Rdi: result = "RCX"
  of Rbp: result = "RCX"
  of Rsp: result = "RCX"
  of R8: result = "R8"
  of R9: result = "R9"
  of R10: result = "R10"
  of R11: result = "R11"
  of R12: result = "R12"
  of R13: result = "R13"
  of R14: result = "R14"
  of R15: result = "R15"
  else: result = "<bug: invalid register>"

const
  Xmm0 = FloatReg(0)
  Xmm1 = FloatReg(1)
  Xmm2 = FloatReg(2)
  Xmm3 = FloatReg(3)
  Xmm4 = FloatReg(4)
  Xmm5 = FloatReg(5)
  Xmm6 = FloatReg(6)
  Xmm7 = FloatReg(7)
  Xmm8 = FloatReg(8)
  Xmm9 = FloatReg(9)
  Xmm10 = FloatReg(10)
  Xmm11 = FloatReg(11)
  Xmm12 = FloatReg(12)
  Xmm13 = FloatReg(13)
  Xmm14 = FloatReg(14)
  Xmm15 = FloatReg(15)

  LastFloatReg = Xmm15

proc regName*(r: FloatReg): string =
  result = "XMM"
  result.addInt int(r)

const
  CarryFlag* = CpuFlag(0)
  ParityFlag* = CpuFlag(2)
  AuxFlag* = CpuFlag(4)
  ZeroFlag* = CpuFlag(6)
  SignFlag* = CpuFlag(7)
  TrapFlag* = CpuFlag(8)
  InterruptFlag* = CpuFlag(9)
  DirFlag* = CpuFlag(10)
  OverflowFlag* = CpuFlag(11)
  UndefinedFlag* = CpuFlag(255)
  # Other flags not modelled as we don't need them.

proc flagName*(f: CpuFlag): string =
  case f
  of CarryFlag: "CF"
  of ParityFlag: "PF"
  of AuxFlag: "AF"
  of ZeroFlag: "ZF"
  of SignFlag: "SF"
  of TrapFlag: "TF"
  of InterruptFlag: "IF"
  of DirFlag: "DF"
  of OverflowFlag: "OF"
  else: "<bug: invalid flag>"


const
  WordSize* = 8
  StackAlign = 16
  HomeSpace* = 32

type
  RegAllocator* = object
    used: set[IntReg]
    usedFloats: set[FloatReg]
    usedStackSpace, maxStackSpace: int
    scratchStackSlot: int

proc initRegAllocator*(): RegAllocator =
  result = RegAllocator(scratchStackSlot: -1)

proc getScratchStackSlot*(a: var RegAllocator): int =
  if a.scratchStackSlot < 0:
    a.scratchStackSlot = a.usedStackSpace
    inc a.usedStackSpace, WordSize
  result = a.scratchStackSlot

proc getReg*(a: var RegAllocator): IntReg =
  result = IntReg(0)
  while result <= LastIntReg and result in a.used:
    inc result
  if result > LastIntReg:
    raiseAssert "out of integer registers"
  incl a.used, result

proc freeReg*(a: var RegAllocator; r: IntReg) =
  assert r in a.used, "attempt to free an already free register"
  excl a.used, r

type
  LocKind* = enum
    Undef,
    ImmediateInt,
    ImmediateUInt,
    ImmediateFloat,
    InReg,
    InRegFp,
    InStack,
    InFlag, # in a CPU flag
    JumpMode # not a value, but control flow
    InData # in some global data section
    InTls  # in thread local storage
    InRegOffset # address is (reg + offset)
    InRegRegScaledOffset # address is (reg + reg*scale + offset)
  LocFlag* = enum
    Reg1Temp, # reg1 is temp
    Reg2Temp, # reg2 is temp
    Indirect  # we only have the address of the thing, not the thing itself
    Reg1NeedsPop
    Reg2NeedsPop
  Location* = object
    typ*: AsmSlot # this already has an `offset` field that is used for `InRegOffset` etc.
    flags*: set[LocFlag]
    case kind*: LocKind
    of Undef: discard
    of ImmediateInt: ival*: int64
    of ImmediateUInt: uval*: uint64
    of ImmediateFloat: fval*: float
    of InReg, InRegOffset, InRegRegScaledOffset:
      reg1*, reg2*: IntReg
    of InRegFp: regf*: FloatReg
    of InStack: slot*: int
    of InFlag: flag*: TagId
    of JumpMode: label*: int
    of InData, InTls: data*: StrId

proc immediateLoc*(ival: int64; typ: AsmSlot): Location = Location(typ: typ, kind: ImmediateInt, ival: ival)
proc immediateLoc*(uval: uint64; typ: AsmSlot): Location = Location(typ: typ, kind: ImmediateUInt, uval: uval)
proc immediateLoc*(fval: float; typ: AsmSlot): Location = Location(typ: typ, kind: ImmediateFloat, fval: fval)
proc stringData*(data: StrId): Location = Location(kind: InData, data: data)

proc allocResultWin64*(a: var RegAllocator;
                       returnType: AsmSlot;
                       returnLoc: var Location) =
  if returnType.kind == AFloat:
    # But no reason to mark it as used!
    returnLoc = Location(kind: InRegFp, regf: Xmm0)
  elif returnType.size in [1, 2, 4, 8]:
    # But no reason to mark it as used!
    returnLoc = Location(kind: InReg, reg1: Rax)
  else:
    # the tricky part:
    returnLoc = Location(flags: {Indirect}, kind: InReg, reg1: Rcx)
    incl a.used, Rcx

proc stackSpaceResultWin64*(returnType: AsmSlot): int =
  if returnType.kind == AFloat:
    result = 0 # no stack space required for the result
  elif returnType.size in [1, 2, 4, 8]:
    result = WordSize # passed back in Rax
  else:
    result = align(returnType.size, 8)

proc resultWin64*(returnType: AsmSlot): Location =
  # But no reason to mark anything as used!
  if returnType.kind == AFloat:
    result = Location(kind: InRegFp, regf: Xmm0)
  elif returnType.size in [1, 2, 4, 8]:
    # But no reason to mark it as used!
    result = Location(kind: InReg, reg1: Rax)
  else:
    # the tricky part:
    result = Location(kind: InReg, reg1: Rax)

proc allocParamWin64*(a: var RegAllocator; param: AsmSlot): Location =
  if param.kind == AFloat:
    # see https://learn.microsoft.com/en-us/cpp/build/x64-calling-convention?view=msvc-170
    # Use XMM0L, XMM1L, XMM2L, and XMM3L.
    block floatRegSearch:
      for xmmIndex in 0..3:
        let xmm = FloatReg(xmmIndex)
        if not a.usedFloats.contains(xmm):
          incl a.usedFloats, xmm
          result = Location(kind: InRegFp, regf: xmm)
          break floatRegSearch
      result = Location(kind: InStack, slot: a.usedStackSpace)
      inc a.usedStackSpace, WordSize
  else:
    let flags = if param.size notin [1, 2, 4, 8]: {Indirect} else: {}
    const attempts = [Rcx, Rdx, R8, R9]
    block intRegSearch:
      for att in attempts:
        if not a.used.contains(att):
          incl a.used, att
          result = Location(flags: flags, kind: InReg, reg1: att)
          break intRegSearch
      result = Location(flags: flags, kind: InStack, slot: a.usedStackSpace)
      inc a.usedStackSpace, WordSize

proc reverseStackParamsWin64*(res: var openArray[Location]) =
  # reverse the stack slots since the ABI says stack slots
  # are passed from right to left:
  var front = 0
  var back = res.len - 1
  while front < back:
    if res[front].kind == InStack:
      while front < back and res[back].kind != InStack: dec back
      if front >= back: break
      assert res[back].kind == InStack
      swap res[front].slot, res[back].slot
      dec back
    inc front

proc allocParamsWin64*(a: var RegAllocator;
                       params: openArray[AsmSlot];
                       res: var openArray[Location]) =
  # Windows ABI specific code here!
  assert params.len == res.len
  for i in 0 ..< params.len:
    res[i] = allocParamWin64(a, params[i])
  reverseStackParamsWin64 res

proc allocStack(a: var RegAllocator; slot: AsmSlot): Location =
  a.usedStackSpace = align(a.usedStackSpace, slot.align)
  result = Location(kind: InStack, slot: a.usedStackSpace)
  inc a.usedStackSpace, slot.size

proc selectReg(a: var RegAllocator; slot: AsmSlot; regs: openArray[IntReg]): Location =
  for reg in regs:
    if not a.used.contains(reg):
      a.used.incl reg
      return Location(kind: InReg, reg1: reg)
  # use the stack:
  result = allocStack(a, slot)

const
  allAttempts = [Rax, Rbx, Rcx, Rdx, Rsi, Rdi, Rbp, R8, R9, R10, R11, R12, R13, R14, R15]

proc scratchReg*(a: var RegAllocator): Location =
  for reg in allAttempts:
    if not a.used.contains(reg):
      a.used.incl reg
      return Location(flags: {Reg1Temp}, kind: InReg, reg1: reg)
  result = Location(kind: Undef)

proc allocVar*(a: var RegAllocator; slot: AsmSlot; props: VarProps): Location =
  # "The x64 ABI considers registers RBX, RBP, RDI, RSI, RSP, R12, R13, R14, R15, and XMM6-XMM15
  # nonvolatile. They must be saved and restored by a function that uses them."
  const
    safeAttempts = [Rbx, Rbp, Rdi, Rsi, R12, R13, R14, R15]
  #   ^ of course you cannot list the stack pointer Rsp here!

  if AddrTaken in props:
    # we must use the stack:
    result = allocStack(a, slot)
  elif slot.kind == AFloat:
    let start = if AllRegs in props: 0 else: 6
    for xmmIndex in start..15:
      let xmm = FloatReg(xmmIndex)
      if not a.usedFloats.contains(xmm):
        incl a.usedFloats, xmm
        return Location(kind: InRegFp, regf: xmm)
    result = Location(kind: InStack, slot: a.usedStackSpace)
    inc a.usedStackSpace, 8
  else:
    if slot.size <= WordSize:
      # consider using a register
      if AllRegs in props:
        result = selectReg(a, slot, allAttempts)
      else:
        result = selectReg(a, slot, safeAttempts)
    else:
      # use the stack:
      result = allocStack(a, slot)

proc freeLocEnforced*(a: var RegAllocator; loc: Location) =
  case loc.kind
  of InReg, InRegOffset:
    a.used.excl loc.reg1
  of InRegFp:
    a.usedFloats.excl loc.regf
  of InRegRegScaledOffset:
    a.used.excl loc.reg1
    a.used.excl loc.reg2
  else:
    discard "nothing to do"

proc freeTempRaw*(a: var RegAllocator; loc: Location) =
  case loc.kind
  of InReg, InRegOffset:
    if Reg1Temp in loc.flags:
      a.used.excl loc.reg1
  of InRegFp:
    if Reg1Temp in loc.flags:
      a.usedFloats.excl loc.regf
  of InRegRegScaledOffset:
    if Reg1Temp in loc.flags:
      a.used.excl loc.reg1
    if Reg2Temp in loc.flags:
      a.used.excl loc.reg2
  else:
    discard "nothing to do"

proc freeScope*(a: var RegAllocator; vars: openArray[Location]) =
  # useful when we know that a scope exit is about to happen.
  # We then free stack slots so that they can be reused.
  a.maxStackSpace = max(a.maxStackSpace, a.usedStackSpace)
  var m = a.usedStackSpace
  for loc in vars:
    case loc.kind
    of InReg, InRegOffset:
      a.used.excl loc.reg1
    of InRegRegScaledOffset:
      a.used.excl loc.reg1
      a.used.excl loc.reg2
    of InRegFp:
      a.usedFloats.excl loc.regf
    of InStack:
      m = min(m, loc.slot)
    else:
      discard "nothing to do"
  a.usedStackSpace = m

proc genProlog*(a: RegAllocator) =
  discard

proc genEpilog*(a: RegAllocator) =
  discard

proc opcodeSuffix*(s: AsmSlot): string =
  if s.kind == AFloat:
    case s.size
    of 4: "s" # single
    of 8: "l" # long
    of 10: "t" # ten bytes (80-bit floating point)
    else: "bug"
  else:
    case s.size
    of 1: "b" # byte
    of 2: "w" # word
    of 4: "l" # long
    of 8: "q" # quad
    else: "bug"

proc inMemory*(a: Location): bool {.inline.} = a.kind in {InStack, InData, InRegOffset, InRegRegScaledOffset}
proc isImmediate*(a: Location): bool {.inline.} = a.kind in {ImmediateInt, ImmediateUInt, ImmediateFloat}

proc invalidCombination*(a, b: Location): bool =
  if a.inMemory and b.inMemory:
    result = true
  elif a.isImmediate and b.isImmediate:
    result = true
  else:
    result = false

proc sameLocation*(a, b: Location): bool =
  if a.kind == b.kind:
    case a.kind
    of Undef: result = true
    of InStack:
      result = a.slot == b.slot
    of ImmediateInt:
      result = a.ival == b.ival
    of ImmediateUInt:
      result = a.uval == b.uval
    of ImmediateFloat:
      result = a.fval == b.fval
    of InReg:
      result = a.reg1 == b.reg1
    of InRegOffset:
      result = a.reg1 == b.reg1 and a.typ.offset == b.typ.offset
    of InRegRegScaledOffset:
      result = a.reg1 == b.reg1 and a.reg2 == b.reg2 and
        a.typ.offset == b.typ.offset and a.typ.size == b.typ.size
    of InRegFp:
      result = a.regf == b.regf
    of JumpMode:
      result = a.label == b.label
    of InFlag:
      result = a.flag == b.flag
    of InData, InTls:
      result = a.data == b.data
  else:
    result = false
