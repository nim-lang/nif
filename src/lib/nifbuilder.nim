#       Nif library
# (c) Copyright 2024 Andreas Rumpf
#
# See the file "license.txt", included in this
# distribution, for details about the copyright.

## Support code for generating NIF code.

# Idea: enforce "not used after `freeze`" at compile time thanks to sink params
# and disabled copies.
type
  Builder* = object

proc `=copy`(dest: var Builder; src: Builder) {.error.}

type
  View* = object

proc freeze(b: sink Builder): View = View()
