# nifgram tool

Nifgram is a tool that reads a NIF grammar (also written down in NIF syntax)
and generates Nim code that traverses a NIF file according to this grammar.
The grammar has lots of customization points so that actions can be attached
to the matched construct.

See `nifc/nifc_grammar.nif` for a somewhat realistic example.
