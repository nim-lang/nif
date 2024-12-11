#       Nimony
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Types required by semantic checking.

import std / [tables, sets, os, syncio, formatfloat, assertions]
include nifprelude
import nimony_model, symtabs, builtintypes, decls, symparser,
  programs, sigmatch, magics, reporters, nifconfig, nifindexes

import ".." / gear2 / modnames

type
  TypeCursor* = Cursor
  SemRoutine* {.acyclic.} = ref object
    kind*: SymKind
    inGeneric*, inLoop*, inBlock*: int
    returnType*: TypeCursor
    resId*: SymId
    parent*: SemRoutine

proc createSemRoutine*(kind: SymKind; parent: SemRoutine): SemRoutine =
  result = SemRoutine(kind: kind, parent: parent, resId: SymId(0))

const
  MaxNestedTemplates* = 100

type
  ImportedModule* = object
    iface*: Iface

  InstRequest* = object
    origin*: SymId
    targetSym*: SymId
    #targetType*: TypeCursor
    #typeParams*: seq[TypeCursor]
    inferred*: Table[SymId, Cursor]
    requestFrom*: seq[PackedLineInfo]

  ProcInstance* = object
    targetSym*: SymId
    procType*: TypeCursor
    returnType*: TypeCursor

  ProgramContext* = ref object # shared for every `SemContext`
    config*: NifConfig

  ObjField* = object
    sym*: SymId
    level*: int # inheritance level
    typ*: TypeCursor

  SemContext* = object
    dest*: TokenBuf
    routine*: SemRoutine
    currentScope*: Scope
    g*: ProgramContext
    typeRequests*, procRequests*: seq[InstRequest]
    includeStack*: seq[string]
    #importedModules: seq[ImportedModule]
    instantiatedFrom*: seq[PackedLineInfo]
    importTab*: Iface
    globals*, locals*: Table[string, int]
    types*: BuiltinTypes
    typeMem*: Table[string, TokenBuf]
    instantiatedTypes*: OrderedTable[string, SymId]
    instantiatedProcs*: OrderedTable[string, ProcInstance]
    thisModuleSuffix*: string
    processedModules*: HashSet[string]
    usedTypevars*: int
    templateInstCounter*: int
    #fieldsCache: Table[SymId, Table[StrId, ObjField]]
