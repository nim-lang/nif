# PreASM - the NIF based pre-assembler

NIFC is close to C but what if we want to generate native code directly? It
turns out C is quite away from machine code and closer to conventional high
level languages from the 80ies such as Pascal.

"PreASM" is a language that is close to assembler language. PreASM does essentially
these transformations:

- Object fields accesses and array indexing are turned into address computations
  and loads and stores. Local variables are turned into abstract stack slots.
- NIFC operations like `eq` get an explicit type too.
- All control flow is done with labels and `jmp`.

PreASM is CPU **independent**, it can be seen as a general purpose IR. It's
suitable for direct interpretation or for native code generation.


## Considered and rejected idea(s)

- The `call` instructions are "unnested" as CPUs do not supported "nested" calls.
  For example `(call f (call g))` is turned into `(let tmp (call g)) (call f tmp)`.
  Note that other nestings like `(add x (sub y -1))` are left as they are so that
  a primitive code generator can combine these easily to a single CPU instruction.

**Rationale**: It's the one place where PreASM introduces temporaries on its own
and it's currently unclear if any consumer of PreASM would benefit from it as
a code generator in general has to "unnest" everything else anyway.
