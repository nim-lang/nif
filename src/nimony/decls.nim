#       Nimony
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Helpers for declarative constructs like `let` statements or `proc` declarations.

import nifstreams, nifcursors
import ".." / specs / tags

proc isRoutine*(t: TagId): bool {.inline.} =
  t == ProcT or t == FuncT or t == IteratorT or t == MacroT or
  t == TemplateT or t == ConverterT or t == MethodT

proc isLocal*(t: TagId): bool {.inline.} =
  t == LetT or t == VarT or t == ConstT or t == ParamT or t == TypevarT or
  t == CursorT or t == FldT

type
  Local* = object
    tag*: TagId
    name*: Cursor
    exported*: Cursor
    pragmas*: Cursor
    typ*: Cursor
    val*: Cursor

proc asLocal*(c: Cursor): Local =
  var c = c
  let t = c.tag
  result = Local(tag: t)
  if isLocal(t):
    inc c
    result.name = c
    skip c
    result.exported = c
    inc c
    result.pragmas = c
    skip c
    result.typ = c
    skip c
    result.val = c
  else:
    result.tag = ErrT

type
  Routine* = object
    tag*: TagId
    name*: Cursor
    exported*: Cursor
    pattern*: Cursor # for TR templates/macros
    typevars*: Cursor # generic parameters
    params*: Cursor
    retType*: Cursor
    effects*: Cursor
    pragmas*: Cursor
    body*: Cursor

proc isGeneric*(r: Routine): bool {.inline.} =
  r.typevars.tag == TypevarsT

proc asRoutine*(c: Cursor): Routine =
  var c = c
  let t = c.tag
  result = Routine(tag: t)
  if isRoutine(t):
    inc c
    result.name = c
    skip c
    result.exported = c
    inc c
    result.pattern = c
    skip c
    result.typevars = c
    skip c
    result.params = c
    skip c
    result.retType = c
    skip c
    result.effects = c
    skip c
    result.pragmas = c
    skip c
    result.body = c
  else:
    result.tag = ErrT

type
  TypeDecl* = object
    tag*: TagId
    name*: Cursor
    exported*: Cursor
    typevars*: Cursor
    pragmas*: Cursor
    body*: Cursor

proc isGeneric*(r: TypeDecl): bool {.inline.} =
  r.typevars.tag == TypevarsT

proc asTypeDecl*(c: Cursor): TypeDecl =
  var c = c
  let t = c.tag
  result = TypeDecl(tag: t)
  if t == TypeT or t == TypaT:
    inc c
    result.name = c
    skip c
    result.exported = c
    inc c
    result.typevars = c
    skip c
    result.pragmas = c
    skip c
    result.body = c
  else:
    result.tag = ErrT

type
  ObjectDecl* = object
    tag*: TagId
    parentType*: Cursor
    firstField*: Cursor

proc asObjectDecl*(c: Cursor): ObjectDecl =
  var c = c
  let t = c.tag
  result = ObjectDecl(tag: t)
  if t == ObjectT:
    inc c
    result.parentType = c
    skip c
    result.firstField = c
  else:
    result.tag = ErrT

type
  EnumDecl* = object
    tag*: TagId
    baseType*: Cursor
    firstField*: Cursor

proc asEnumDecl*(c: Cursor): EnumDecl =
  var c = c
  let t = c.tag
  result = EnumDecl(tag: t)
  if t == EnumT:
    inc c
    result.baseType = c
    skip c
    result.firstField = c
  else:
    result.tag = ErrT

type
  EnumField* = object
    tag*: TagId
    name*: Cursor
    val*: Cursor

proc asEnumField*(c: Cursor): EnumField =
  var c = c
  let t = c.tag
  result = EnumField(tag: t)
  if t == EfldT:
    inc c
    result.name = c
    skip c
    result.val = c
  else:
    result.tag = ErrT

type
  ForStmt* = object
    tag*: TagId
    iter*, vars*, body*: Cursor

proc asForStmt*(c: Cursor): ForStmt =
  var c = c
  let t = c.tag
  result = ForStmt(tag: t)
  if t == ForT:
    inc c
    result.iter = c
    skip c
    result.vars = c
    skip c
    result.body = c
  else:
    result.tag = ErrT
