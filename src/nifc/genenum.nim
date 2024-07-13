
const
  code = """
Lvalue ::= Symbol | (deref Expr) |
             (at Expr Expr) | # array indexing
             (dot Expr Symbol Number) | # field access
             (pat Expr Expr) | # pointer indexing

Expr ::= Number | CharLiteral | StringLiteral |
         Lvalue |
         (par Expr) | # wraps the expression in parentheses
         (addr Lvalue) | # "address of" operation
         (nil) | (false) | (true) |
         (and Expr Expr) | # "&&"
         (or Expr Expr) | # "||"
         (not Expr) | # "!"
         (sizeof Expr) |
         (constr Type Expr*) |
         (kv Expr Expr) |

         (add Type Expr Expr) |
         (sub Type Expr Expr) |
         (mul Type Expr Expr) |
         (div Type Expr Expr) |
         (mod Type Expr Expr) |
         (shr Type Expr Expr) |
         (shl Type Expr Expr) |
         (bitand Type Expr Expr) |
         (bitor Type Expr Expr) |
         (bitnot Type Expr Expr) |
         (eq Expr Expr) |
         (neq Expr Expr) |
         (le Expr Expr) |
         (lt Expr Expr) |
         (cast Type Expr) |
         (call Expr+ )

BranchValue ::= Number | CharLiteral | Symbol
BranchRange ::= BranchValue | (range BranchValue BranchValue)
BranchRanges ::= (ranges BranchRange+)

VarDecl ::= (var SymbolDef VarPragmas Type [Empty | Expr])
ConstDecl ::= (const SymbolDef VarPragmas Type Expr)
EmitStmt ::= (emit Expr+)

Stmt ::= Expr |
         VarDecl |
         ConstDecl |
         EmitStmt |
         (asgn Lvalue Expr) |
         (if (elif Expr StmtList)+ (else StmtList)? ) |
         (while Expr StmtList) |
         (case Expr (of BranchRanges StmtList)* (else StmtList)?) |
         (lab SymbolDef) |
         (jmp Symbol) |
         (tjmp Expr Symbol) | # jump if condition is true
         (fjmp Expr Symbol) | # jump if condition is false
         (ret Expr) # return statement

StmtList ::= (stmts Stmt*)

Params ::= Empty | (params Param*)

ProcDecl ::= (proc SymbolDef Params Type ProcPragmas [Empty | StmtList])

FieldDecl ::= (fld SymbolDef FieldPragmas Type)

UnionDecl ::= (union Empty FieldDecl*)
ObjDecl ::= (object [Empty | Type] FieldDecl*)
EnumFieldDecl ::= (efld SymbolDef Expr)
EnumDecl ::= (enum Type EnumFieldDecl+)

ProcType ::= (proctype Empty Params Type ProcTypePragmas)

IntQualifier ::= (atomic) | (ro)
PtrQualifier ::= (atomic) | (ro) | (restrict)

Type ::= Symbol |
         (i IntBits IntQualifier*) |
         (u IntBits IntQualifier*) |
         (f IntBits IntQualifier*) |
         (c IntBits IntQualifier*) | # character types
         (bool IntQualifier*) |
         (void) |
         (ptr Type PtrQualifier) | # pointer to a single object
         (array Type Expr) |
         (flexarray Type) |
         (aptr Type PtrQualifier) | # pointer to an array of objects
         ProcType
TypeDecl ::= (type SymbolDef TypePragmas [Type | ObjDecl | UnionDecl | EnumDecl])

CallingConvention ::= (cdecl) | (stdcall)
Attribute ::= (attr StringLiteral)
ProcPragma ::= (inline) | CallingConvention | (varargs) | (was Identifier) |
               (selectany) | Attribute
ProcTypePragma ::= CallingConvention | (varargs) | Attribute

ProcTypePragmas ::= Empty | (pragmas ProcTypePragma+)
ProcPragmas ::= Empty | (pragmas ProcPragma+)

CommonPragma ::= (align Number) | (was Identifier) | Attribute
VarPragma ::= CommonPragma | (tls)
VarPragmas ::= Empty | (pragmas VarPragma+)

FieldPragma ::= CommonPragma | (bits Number)
FieldPragmas ::= (pragmas FieldPragma+)

TypePragma ::= CommonPragma | (vector Number)
TypePragmas ::= Empty | (pragmas TypePragma+)


ExternDecl ::= (imp ProcDecl | VarDecl | ConstDecl)

TopLevelConstruct ::= ExternDecl | ProcDecl | VarDecl | ConstDecl |
                      TypeDecl | EmitStmt
Include ::= (incl StringLiteral)
Module ::= (stmts Include* TopLevelConstruct*)
"""

import std / [sets, strutils, sequtils]

proc extract(s: string) =
  var i = 0
  var keyw = newSeq[string]()
  while i < s.len:
    if s[i] == '(':
      var j = i+1
      while j < s.len and s[j] notin {' ', '\n', ')'}: inc j
      keyw.addUnique substr(s, i+1, j-1)
    inc i
  for k in keyw:
    echo "    ", k[0].toUpperAscii, k[1..^1], "C = \"", k, "\""

extract code
