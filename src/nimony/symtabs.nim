#       Nimony
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

import std / [tables]
import "../.." / nif / src / lib / [nifstreams]
import compat

type
  Sym* = object
    name*: SymId
    tag*: TagId
    pos*: int32

  ScopeKind* = enum
    NormalScope, ToplevelScope, ImportScope
  Scope* {.acyclic.} = ref object
    tab*: Table[StrId, seq[Sym]] # 'seq' because of overloading
    undo: seq[Table[StrId, int]] # len of 'key' to reset tab[key] to.
    up*: Scope
    kind*: ScopeKind
    rolledBack: bool

proc openShadowScope*(s: Scope) =
  s.undo.add initTable[StrId, int]()

proc commitShadowScope*(s: Scope) =
  if not s.rolledBack:
    let newLen = s.undo.len - 1
    s.undo.myshrink newLen

proc rollbackShadowScope*(s: Scope) =
  let last = s.undo.len - 1
  for k, oldLen in pairs(s.undo[last]):
    s.tab[k].myshrink oldLen
  s.rolledBack = true

proc remember(s: Scope; name: StrId) {.inline.} =
  let last = s.undo.len - 1
  if last >= 0:
    if not s.undo[last].hasKey(name):
      s.undo[last][name] = s.tab.getOrDefault(name).len

proc rememberZero(s: Scope; name: StrId) {.inline.} =
  let last = s.undo.len - 1
  if last >= 0:
    if not s.undo[last].hasKey(name):
      s.undo[last][name] = 0

proc addOverloadable*(s: Scope; name: StrId; sym: Sym) =
  s.remember name
  s.tab.mgetOrPut(name, @[]).add sym

type
  AddStatus* = enum
    Conflict, Success

proc addNonOverloadable*(s: Scope; name: StrId; sym: Sym): AddStatus =
  let existing = s.tab.getOrDefault(name)
  if existing.len == 0:
    # no error
    s.rememberZero name
    s.tab.mgetOrPut(name, @[]).add sym
    result = Success
  else:
    # error: symbol already exists of the same name:
    result = Conflict
