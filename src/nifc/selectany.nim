#       Nif library
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

# imported from codegen.nim

##[

Helpers for the `(selectany)` feature. There is no good portable
solution to get this feature for C so we make use of the preprocessor:

select_any.h:

#include "mod_a.h"
#include "mod_b.h"

------------------------------

mod_a.h:
#ifndef genericProc__impl
#  define genericProc__impl
#  define genericProc__a
#endif

------------------------------

mod_b.h:
#ifndef genericProc__impl
#  define genericProc__impl
#  define genericProc__b
#endif

------------------------------

mod_a.c:

#include "select_any.h"
void genericProc() // always declare header
#ifdef genericProc__a
{ ... } // provide an implementation
#else
; // implementation is elsewhere
#endif

------------------------------

mod_b.c:

#include "select_any.h"
void genericProc() // always declare header
#ifdef genericProc__b
{ ... } // provide an implementation
#else
; // implementation is elsewhere
#endif

]##

proc genRoutineGuardBegin(c: var GeneratedCode; f: var CppFunc) =
  let guardName = c.tokens[f.e.name] & "__" & $c.m.canonName

  c.headerFile.add c.tokens.getOrIncl"""#ifndef """
  c.headerFile.add f.e.name
  c.headerFile.add "__impl"
  c.headerFile.add NewLine

  c.headerFile.add "  #define "
  c.headerFile.add f.e.name
  c.headerFile.add "__impl"
  c.headerFile.add NewLine

  c.headerFile.add "  #define "
  c.headerFile.add guardName
  c.headerFile.add NewLine

  c.headerFile.add "#endif"
  c.headerFile.add NewLine

  emit NewLine
  emit "#ifdef "
  emit guardName
  emit NewLine


proc genRoutineGuardEnd(c: var GeneratedCode) =
  emit "#else"
  emit NewLine
  emit Semicolon
  emit "#endif"
  emit NewLine
  emit NewLine
