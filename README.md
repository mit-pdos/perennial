# Verifying concurrent, crash-safe systems with Perennial

[![Build Status](https://github.com/mit-pdos/perennial/workflows/CI/badge.svg)](https://github.com/mit-pdos/perennial/actions?query=workflow%3ACI)

Perennial is a system for verifying correctness for systems with both
concurrency and crash-safety requirements, including recovery procedures. For
example, think of file systems, concurrent write-ahead logging like Linux's jbd2
layer, and persistent key-value stores like RocksDB.

Perennial uses [Goose](https://github.com/tchajed/goose) to enable verification
of programs written in (a subset of) Go.

This repository also includes a proof of the transaction system in
[goose-nfsd](https://github.com/mit-pdos/goose-nfsd), including a simple NFS
server built on top.

## Compiling

We develop Perennial using Coq master and maintain compatibility with Coq 8.13.

This project uses git submodules to include several dependencies. You should run `git submodule update --init --recursive` to set that up.

To compile just run `make` with Coq on your `$PATH`.

We compile with [coqc.py](etc/coqc.py), a Python wrapper around `coqc` to get
timing information. The wrapper requires Python3 and the `argparse` library. You
can also compile without timing information with `make TIMED=false`.

## Compilation times

Perennial takes about 70-80 CPU minutes to compile. Compiling in parallel with `make -j4` is significantly faster, and can cut the time down to 20-25 minutes.

Incremental builds are better, after Iris and some core libraries are compiled.

When you make a change to a dependency, you can keep working without fully
compiling the dependency by compiling `vos` interface files, which skips proofs.
The simplest way to do this is just to run `make vos`, but it's fastest to pass
a specific target, like `make src/program_proof/wal/proof.required_vos`, which
only builds the vos dependencies to work on the `wal/proof.v` file.

If you're working on Goose and only need to re-check the Goose output, you can run `make interpreter` to run the interpreter's semantics tests, or directly compile just the Goose output files.

Coq also has a feature called `vok` files, where `coqc` compiles a `vos` file
without requiring its dependencies to be built. The process does not produce a
self-contained `vo` file, but emits an empty `vok` file to record that checking
is complete. This allows checking individual files completely and in parallel.
Using `vos` and `vok` files can significantly speed up the edit-compile-debug
cycle. Note that technically `vok` checking isn't the same as regular compilation - it doesn't check universe constraints in the same way.

## Source organization

`src/`

- `program_logic/`
  The main library that implements the crash safety reasoning in Perennial. This
  includes crash weakest preconditions, crash invariants, idempotence, and crash
  refinement reasoning.

- `goose_lang/`
  A lambda calculus with memory, concurrency, and an "FFI" to some external
  world, which can be instantiated to provide system calls specified using a
  relation over states.

  This language is the target of Goose and thus models Go and also implements
  the Iris `language` and Perennial `crash_lang` interfaces for proofs using
  Perennial.

  This directory includes a lifting to ghost state that supports more standard
  points-to facts, compared to the semantics which specifies transitions over
  the entire state. It also proves Hoare triples using these resources for the
  primitives of the language.

  - `typing.v`
    A type system for GooseLang. This type system is used as part of the
    `typed_mem/` machinery. TODO: there's much more to say here.

  - `lib/`
    GooseLang is partly a shallow embedding - many features of Go are
    implemented as implementations. These features are divided into several
    libraries. Each library has an implementation and a proof file. For example,
    `map/impl.v` implements operations maps using GooseLang's sums while
    `map/map.v` proves Hoare triples for the implementation. Separating the
    implementation allows us to run the implementation in the GooseLang
    interpreter without compiling the proofs.
    - `typed_mem/`
      Implements support for flattening products over several contiguous
      locations, which is the foundation for supporting struct fields as
      independent entities. The proofs build up reasoning about the `l ↦[t] v`
      assertion, which says `l` points to a value `v` of type `t` (in the
      GooseLang type system). If `t` is a composite type, this assertion owns
      multiple physical locations.
    - `struct/`
      Implements struct support. Structs are essentially tuples with names for
      the fields. The theorems proven here culminate in a way to split a typed
      points-to for a struct into its individual fields.
    - `slice/`
      Implements Go slices using a tuple of an array, length, and capacity.
    - `map/`
      Implements Go maps as a linked list of key-value pairs, terminating in a
      default value.
    - `loop/`
      Implements a combinator for loops on top of the basic recursion support.
    - `lock/`
      Implements locks and condition variables using a spin lock, which is
      implemented using `CmpXchg`.
    - `encoding/`
      Implements uint64 and uint32 little-endian encoding.
  - `examples/`
    The Goose unit tests; these are auto-generated from the Goose repo, from
    `internal/examples/`.
  - `interpreter/`
    An interpreter for sequential GooseLang, equipped with a proof of partial
    correctness: if the interpreter produces a result, the semantics also can.

    This is used to implement tests in `generated_test.v`. These tests are Go
    functions which return booleans that should be true; we check this using Go
    test, and compare against the interpreter's behavior.

  - `ffi/`

    Two different FFIs to plug into `GooseLang` - `disk.v` is the one we
    actually use, while `append_log.v` is the FFI-based specification for the
    `append_log` example.

* `program_proof/`

  The proofs about programs we have so far.

  - `append_log_proof.v` Hoare triples about the `append_log` example, which is
    implemented in the Goose repo at `internal/examples/append_log/` and
    extracted to `goose_lang/examples/append_log/`.

  - `examples/` Examples we wrote for POPL

  - `wal/`, `txn/`, and `buftxn/` proof of the transaction system library in
    goose-nfsd

  - `simple/` proof of a simple NFS server

* `Helpers/`

  - `Integers.v`
    Wrapper around `coqutil`'s word library for u64, u32, and u8.
  - `Transitions.v`
    A library for writing relations in a monadic, combinator style.
  - `NamedProps.v`
    An Iris library for naming hypotheses within definitions and using them to
    automatically destruct propositions.
  - other files are basically standard library extensions

* `algebra/`

  Additional CMRAs for Iris ghost variables

It's also worth noting that `external/Goose` contains committed copies of the
Goose output on some real code we have. This includes
`github.com/tchajed/marshal` and `github.com/mit-pdos/goose-nfsd`. The directory
structure here mirrors the way Go import paths work.

## Publications

Perennial 1 is described in our SOSP paper, "[Verifying concurrent, crash-safe
systems with Perennial](https://www.chajed.io/papers/perennial:sosp2019.pdf)".
The actual codebase was quite different at the time of this paper; it notably
used a shallow embedding of Goose and did not have WPCs or any of the associated
program logic infrastructure.

Goose is briefly described in a CoqPL extended abstract and associated talk,
"[Verifying concurrent Go code in Coq with
Goose](https://www.chajed.io/papers/goose:coqpl2020.pdf)".

The verified interpreter and test framework for Goose is described in Sydney Gibson's masters thesis, "[Waddle: A proven interpreter and test framework for a subset of the Go semantics](https://pdos.csail.mit.edu/papers/gibsons-meng.pdf)".
