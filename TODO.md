# TODO

- The michelson standard library is temporary embedded into an input file (cf. the head of `examples/boomerang.tzw`).
- The axiom for distinguishing addresse of known contracts are missing, and currently user gives it (cf. Lien 68 in `examples/dexter2/liquidity.tzw`).
- Handling of the default entrypoint is unsound in some case.  It will happen when a known contract calls a default entrypoint of sum type.
