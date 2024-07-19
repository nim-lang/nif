# nif

The NIF data format is a text based file format designed for compiler frontend/backend
communication or communication between different programming languages. The design is
heavily tied to Nim's requirements. However, the design works on language agnostic ASTs
and is so extensible that other programming languages will work well with it too.

A NIF file corresponds to a "module" in the source language. The module is stored as an AST.
The AST consists of "atoms" and "compound nodes".

Documentation
-------------

Docs are here: https://github.com/nim-lang/nif/blob/master/doc/nif-spec.md


Design goals
------------

- Simple to parse.
- Simple to generate.
- Text representation that tends to produce small code.
- Extensible and easily backwards compatible with earlier versions.
- Lossless conversion back to the source code is possible.
- Can be as high level or as low level as required because statements, expressions
  and declarations can be nested arbitrarily.
- Lots of search&replace like operations can be performed reliably with pure text
  manipulation. No parsing step is required for these.
- Readable and writable for humans. However, it is not optimized for this task.

Extensibility is primarily achieved by using two different namespaces. One namespace
is used for "node kinds" and a different one for source level identifiers. This does
away with the notion of a fixed set of "keywords". In NIF new "keywords" ("node kinds")
can be introduced without breaking any code.


Why yet another data format?
----------------------------

Other, comparable formats (LLVM Bitcode or text format, JVM bytecode, .NET bytecode, wasm)
have one or more of the following flaws:

- More complex to parse.
- Too low level representation that loses structured control flow.
- Too low level representation that implies the creation of temporary variables that are
  not in the original source code file.
- Binary formats that make it harder to create tools for.
- Less flexible.
- Cannot express Nim code well.
- Produces bigger files.
