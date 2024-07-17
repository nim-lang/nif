Nim-sem
=======

`Nim-sem` is the name of a NIF dialect that describes Nim 2's AST after the compiler's
"semantic checking" phase. This means that type checking, symbol lookups, macro expansions
compile-time evaluations and overloading resolution have been performed. It is the version
of the AST that is most suitable for tooling and incremental compilation.

By NIF's design Nim's keywords/node kinds, magics and pragmas are all mapped into NIF's
node kind namespace. In other words a magic like `mSizeof` is mapped to `(sizeof)`. Calls
where the first child is a magic symbol `M` are translated to `(M ...)` instead
of `(call M ...)`.

Information that is stored in a `PSym` or `PType` field in Nim are generally turned into
pragmas which are then attached to the sym's declaration side. For example, if `PSym.position`
is set to some value `4` which is not trivially recomputable it would be stored as:

```
(var :theSymbol.2 . (pragmas (position 4)) int .)
```


Sections
--------

Instead of the typical `stmts` root node there are three roots: `deps` ("dependencies"),
`iface` ("interface") and `impl` ("implementation"). An `iface` can be loaded
independently from an `impl`.


Unique module names
-------------------

Every Nim module's absolute file path is turned into a unique, short, machine independent name.
For example `/home/araq/nim/lib/system.nim` is turned into `sys1xfa`. It is not possible to
get back from the short name to the full path. Hence the mapping is stored in the `.nif` file
and while we're at it, we also store a module's checksum:

```
(deps
  (mod mod134ab "/path/to/module.nim" <sha1 of the file's contents>)
)
```

The unique module name is used as a symbol suffix. The N-th `foo` inside module `M` is
encoded as `foo.N.<M's unique module name>`. For local identifiers the module suffix is
left out.

Both `iface` and `impl` can have dependencies. The dependencies are implicitly
stored via the name mangling mechanism. If proc `p` in an `iface` section uses `system.HSlice`
this is encoded as `HSlice.1.sys1xfa` and the suffix can be used to follow this
type to its definition inside `sys1xfa` (which is `system.nim`).


Interface section
-----------------

Because of Nim's `export` feature a module can have symbols in its `iface` that are not "owned"
by it. That means their module suffix differs from the current module's. However, the loading
mechanism for symbols does not need special logic in order to support this feature.


Types
-----

Lisp trees and the symbol mangling to the scheme `<name>.<number>.<module-suffix>` are
sufficient to encode any Nim type into a short descriptive unique name. Many builtin types
like `system.int` are directly mapped to node kinds. For example, like in NIFC `system.int`
becomes `(i M)` and `system.char` becomes `(c 8)`.

More examples:

| type | Encoded as / canonical type description |
| --------- | -------------- |
| `string`  | `(str)`  |
| `seq`  | `(seq)`  |
| `typeof(nil)`  | `(nilt)` |
| `array[2..6, ref MyObj]` | `(array (ref MyObj.1.msfx) (range (i M) 2 6))` |


### Type aliases

Type aliases are immediately resolved and cannot be found in the canonical type description.
Generic type aliases are completely different beasts though and handled differently. To see
why consider this program:

```nim

type
  G[T] = int

proc p[T](x: G[T]) = echo typeof(T)

var v: G[string]
p v
```

It produces "string" as output. Generic type aliases are thus handled like other generic types.


### TypeVars

The position of a "type variable"/"generic parameter" (the `T` in `proc p[T](...)`) is important
for the process of generic instantiation. Every usage of `T` carries its position with it,
`(p T <N>)` (where N is the position) is generated instead of `T`. This makes it much faster
to produce a generic instantiation as no lookup for `T`'s declaration is required.

For example:

```
(type :G.1.m (typevars (typevar :T.1 .)).(object . (fld :FieldName (p T.1 0))))
```

A similar mechanism is used for template parameters.


### Refs

`ref` types are a special beast in Nim. `ref` can be an ordinary structural type.
But it can also be combined with an anonymous object type (`type X = ref object`). It is then
modelled as a different `(refobj)` construct.


Generic routine instantiations
------------------------------

A module does "announce" to its clients the procs that it instantiated. Instantiating these
again in a different module can then be avoided.

For example:

```
(ginst (proc Symbol . TypeVars Params ReturnType))
```

Note that generic **type** instances are not stored in the nim-sem file separately.
The reason is that duplicated type instances are harmless.


Type bound hooks
----------------

A type bound operator like `=copy` for type `T` is not encoded as `(proc :\3Dcopy.3.m ...)` but
instead as `(hook Type RoutineDecl)`.

This makes it easier to lookup hooks for hook synthesis and code generation.

Calls into hooks are compressed. `(call =copy a b)` becomes `(cop a b)`.

| hook name | Node kind in nim-sem |
| --------- | -------------- |
| `=copy`   | `cop` |
| `=sink`   | `snk` |
| `=dup`    | `dup` |
| `=destroy` | `kil` |
| `=trace`   | `trc` |
| `=wasMoved` | `clr` |

Note: Short names have been chosen in anticipation of their frequent use.

Synthesized hooks are stored like other generic instantiations.


Expansions
----------

nim-sem stores the AST after template and macro expansion. This would not allow for
the operation "find all usages of template `>=`". To compensate for this use case nim-sem
has a special section called `expansions` within `impl` that lists every usage/callsite
of a template or macro.


Grammar
-------

Generated nim-sem code must adhere to this grammar. For better readability `'('` and `')'` are written
without quotes and `[]` is used for grouping.

Currently the grammar is simplified and work-in-progress:

```
Empty ::= <according to NIF's spec>
Identifier ::= <according to NIF's spec>
Symbol ::= <according to NIF's spec>
SymbolDef ::= <according to NIF's spec>
Number ::= <according to NIF's spec>
CharLiteral ::= <according to NIF's spec>
StringLiteral ::= <according to NIF's spec>
IntBits ::= [0-9]+ | 'M'

ExportMarker ::= Empty | 'x'

ReturnType ::= Type

Effect ::= (raises Type+) | (sideeffect) | (nosideeffect) | (tags Type+) |
           (gcsafe) | (effectsof Symbol)
Effects ::= Empty | (effects Effect+)

RoutineDecl ::= ($routine SymbolDef ExportMarker TypeVars Params ReturnType
                 Effects Pragmas Body)

GenericInstance ::= (ginst RoutineDecl)

TypeBoundHook ::= (hook Type RoutineDecl)

VarDecl ::= (var SymbolDef ExportMarker Pragmas Type Expr)
LetDecl ::= (var SymbolDef ExportMarker Pragmas Type Expr)
ConstDecl ::= (var SymbolDef ExportMarker Pragmas Type Expr)

Type ::= Symbol | (ref Type) | (ptr Type) | (refobj Type) | (ptrobj Type) |
         (seq Type) | (string) | (i IntBits) | (u IntBits) | (f IntBits) |
         (c 8) | (bool) | (uarray Type) | (lent Type) |
         (p Symbol Number) | # position annotation for a typevar
         (array Type [Type Expr | (range Type Expr Expr)]) |
         (mut Type) | (sink Type) | (out Type) | (stat Type) | # type modifiers
         (invok Type Type (Type+)) | # tyGenericInvokation
         (inst Type Type (Type+)) | # tyGenericInst

BaseClass ::= Empty | Symbol
FieldValue ::= Empty | Expr # default value for object field
Field ::= (fld Symbol ExportMarker Pragmas Type FieldValue)

BranchValue ::= Expr
BranchRange ::= BranchValue | (range BranchValue BranchValue)
BranchRanges ::= (ranges BranchRange+)

CaseObj ::= (case Field (of BranchRanges FieldList)+ (else FieldList)?)
ObjBody ::= Field | CaseObj
FieldList ::= (discard) | ObjBody+
ObjDecl ::= (object BaseClass ObjBody*)

TypeBody ::= ObjDecl | EnumDecl | (distinct Type) | Type

TypeDecl ::= (type SymbolDef ExportMarker TypeVars Pragmas TypeBody)

Decl ::= RoutineDecl | VarDecl | LetDecl | ConstDecl | TypeDecl | TypeBoundHook

Expr ::= Identifier | Symbol | Number | CharLiteral | StringLiteral |
         (at Expr Expr) | (dot Expr Expr) |
         (cast Type Expr) | (conv Type Expr) |
         (call Expr+) | IfExpr | CaseExpr | TryExpr | AnonProc

DiscardStmt ::= (discard Empty | Expr)
ReturnStmt ::= (discard Empty | Expr)
RaiseStmt ::= (discard Empty | Expr)
Stmt ::= DiscardStmt | ReturnStmt | RaiseStmt | IfStmt | CaseStmt |
         ForStmt | WhileStmt | ...

Toplevel ::= Decl |
             (expansions Symbol*) | Stmt

IfaceDecl ::= Decl |
              GenericInstance

Iface ::= (iface IfaceDecl*)
Impl ::= (impl Toplevel*)

Module ::= Iface Impl

```

Notes:

- `$routine` is short for `proc`, `func`, `iterator`, `macro`, `template`, `method`, `converter`.
- `mut` is used for the type modifier `var` as `var` is already used for variable declarations.
