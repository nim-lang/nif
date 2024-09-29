## NIFC Compiler (c) 2024 Andreas Rumpf

## Contains a simple machine agnostic type&size classification system.

type
  AsmTypeKind* = enum
    ABool, # also useful for modelling CPU flag registers
    AInt, AUInt, AFloat, AMem
  AsmSlot* = object
    kind*: AsmTypeKind
    size*, align*, offset*: int # offset is only used for fields and not
                                # really part of a "type" but it's easier this way

  VarProp* = enum
    AddrTaken   # beware: the variable's address has been taken
                # this must also be set for arrays as there is no way to
                # access `a[i]` if `a` itself would be stored in a register
    IsDisjoint  # only `obj.f` is used, not `obj` itself
                # We can then treat `obj.f` as an
                # independent variable
    AllRegs     # variable is used in a basic block that calls no other
                # functions, hence we can consider all registers for
                # its allocation.
  VarProps* = set[VarProp]

proc align*(address, alignment: int): int {.inline.} =
  result = (address + (alignment - 1)) and not (alignment - 1)
