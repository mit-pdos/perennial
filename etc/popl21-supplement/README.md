# Modular reasoning for concurrent storage systems in separation logic with Peony

This is the source code for Peony and verified examples in the framework, as a
supplement to POPL 2021 submission #47.

## Compiling

To compile the Coq development, **in the `peony/` directory** run `make -j4`
with `coqc` on your $PATH. You'll need Coq v8.11, v8.12 beta, or a recent Coq
master. Compiling takes about 25 CPU-minutes, or 10 minutes with a parallel
build.

You can run `make check-assumptions` to compile
`src/program_proof/examples/print_assumptions.vo`, which will print `Closed
under the global context` indicating that the top-level theorems for the
examples are fully proven. Note this is extremely slow and will take a minute or
two.

## Code organization

The main Coq development is in the supplement under `peony/`. Documentation for
this code is still sparse (if the paper is accepted, our artifact will be better
documented).

We provide the original source code for the examples in the top-level
directories `marshal` (a serialization library written in Goose that we
verified) and `peony-examples`. The Goose-translated output is also provided
within `peony/external/Goose/` so that the Coq development is self-contained.

The framework mainly consists of the following directories and specific files:

- `peony/src/program_logic/` develops the Peony program logic in a
  language-independent manner. The main files for the logic are `crash_lang.v`,
  `crash_weakestpre.v`, `recovery_weakestpre.v`, and `recovery_adequacy.v`. Of
  note is also `na_crash_inv.v`, which defines crash invariants (called
  `na_crash_inv` in the source) and proves rules for allocating and opening
  them.
- `peony/src/goose_lang/` implements GooseLang, the target language of the Goose
  tool we use. This directory includes verified libraries for modeling and then
  reasoning about Go as well as plugging GooseLang into the Peony program logic.
  GooseLang is parametrized over durable and other external state; we concretely
  use the implementation in `ffi/disk.v`. In `wpc_proofmode.v` we implement a
  number of tactics to do proofs in the program logic interactively.
- `peony/src/algebra/` has some additional resource algebras (mainly for the
  framework)
- `peony/src/Helpers/` has a variety of general utilities. Of note is
  `ProofCaching.v`, which implements caching support (the implementation does
  not depend on crash reasoning).

The program proofs corresponding to examples in the paper are the following:

- `peony/src/program_proof/marshal_proof.v` verifies a library for encoding
  integers into disk blocks (this is purely in memory; the code in the paper
  glosses over the need for this encoding and pretends like blocks or integers
  are values, to make the exposition smoother)
- `peony/src/program_proof/examples` has the verified examples.
  `replicated_block_proof.v` is a self-contained proof of the entire replicated
  block module. The directory proof is split into `alloc_crash_proof.v` (the
  allocator), `inode_proof.v` (the inode), and `dir_proof.v` (the directory). We
  also verified a single-inode version of the directory (not described in the
  paper) in `single_inode_proof.v` before attempting the full directory proof.
