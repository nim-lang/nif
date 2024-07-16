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
is set to some value `4` which is not trivially recomputable it would be stored like:

```
(var :theSymbol.2 . (pragmas (position 4)) int .)
```


Sections
--------

Instead of the typical `stmts` root node there are two roots: `iface` ("interface")
and `impl` ("implementation"). The `iface` can be loaded independently from `impl`.

Both `iface` and `impl` can have `deps` ("dependencies"). If only the interface is
processed only the interface's dependencies need to be loaded.


Unique module names
-------------------

Every Nim module's absolute file path is


Grammar
-------

Generated nim-sem code must adhere to this grammar. For better readability `'('` and `')'` are written
without quotes and `[]` is used for grouping.

```
Empty ::= <according to NIF's spec>
Identifier ::= <according to NIF's spec>
Symbol ::= <according to NIF's spec>
SymbolDef ::= <according to NIF's spec>
Number ::= <according to NIF's spec>
CharLiteral ::= <according to NIF's spec>
StringLiteral ::= <according to NIF's spec>
IntBits ::= [0-9]+ | 'M'

Iface ::= (iface Decl*)

Decl ::= ($routine SymbolDef ExportMarker TypeVars Params ReturnType Pragmas Body)

```

Notes:

- `$routine` is short for `proc`, `func`, `iterator`, `macro`, `template`, `method`, `converter`.
