# Verifying concurrent, crash-safe systems with Perennial

[![CI](https://github.com/mit-pdos/perennial/actions/workflows/ci.yml/badge.svg)](https://github.com/mit-pdos/perennial/actions/workflows/ci.yml)

Perennial is a system for verifying correctness for systems with both
concurrency and crash-safety requirements, including recovery procedures. It
also includes Grove, an extension for verifying distributed systems, including
reasoning about concurrency, crashes, and recovery of individual nodes. The
program logic is built on top of Iris.

Perennial uses [Goose](https://github.com/goose-lang/goose) to enable verification
of programs written in (a subset of) Go.

This repository also includes proofs for several systems verified using the
Perennial and Grove program frameworks; see the publications list at the bottom for
an overview.

See also [CONTRIBUTING.md](./CONTRIBUTING.md).

## Compiling

We develop Perennial using Rocq master and maintain compatibility with the
latest version of Rocq.

This project uses git submodules to include several dependencies, including
Iris. You should run `git submodule update --init --recursive` to set that up.

To compile just run `make` with rocq on your `$PATH`.

## New goose

We are in the process of migrating to "new Goose", a backwards-incompatible
change to Goose. Most of the Perennial side of the development of new goose is
in `new/`, with the important caveat that new goose is built on top of the core
`goose_lang/` language and its instantiation.

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

- `program_proof/`

  The proofs about programs we have so far. At this point, there are enough that
  it is difficult to keep them documented here. In new goose, proofs are placed
  in predictable locations based on their Go module path, so it is easy to
  identify the source code being verified.

- `Helpers/`

  - `Integers.v`
    Wrapper around `coqutil`'s word library for u64, u32, and u8.
  - `Transitions.v`
    A library for writing relations in a monadic, combinator style.
  - other files are generally standard library extensions, like `List.v`.

- `algebra/`, `iris_lib/`, `base_logic/`

  extensions to Iris.

It's also worth noting that `external/Goose` contains committed copies of the
Goose output on some real code we have. This includes
`github.com/tchajed/marshal` and `github.com/mit-pdos/goose-nfsd`. The directory
structure here mirrors the way Go import paths work.

## Publications

Grove (as well as some examples verified using it) is described in "[Grove: a
Separation-Logic Library for Verifying Distributed
Systems](https://pdos.csail.mit.edu/papers/grove:sosp23.pdf)" from SOSP 2023.

"[Verifying vMVCC, a high-performance transaction library
using multi-version concurrency
control](https://pdos.csail.mit.edu/papers/vmvcc:osdi23.pdf)" corresponds to the
proof in `program_proof/mvcc`.

Goose is briefly described in a CoqPL extended abstract and associated talk,
"[Verifying concurrent Go code in Coq with
Goose](https://www.chajed.io/papers/goose:coqpl2020.pdf)". You can also read
chapter 7 of [Tej
Chajed's PhD thesis](https://www.chajed.io/papers/tchajed-thesis.pdf).

The verified interpreter and test framework for Goose is described in Sydney
Gibson's masters thesis, "[Waddle: A proven interpreter and test framework for a
subset of the Go
semantics](https://pdos.csail.mit.edu/papers/gibsons-meng.pdf)".

The proof of GoJournal's correctness is described in the OSDI paper,
"[GoJournal: a verified, concurrent, crash-safe journaling
system](https://www.chajed.io/papers/gojournal:osdi2021.pdf)". The transaction
system built on top, used for DaisyNFS, is described in Mark Theng's masters
thesis, "[GoTxn: Verifying a Crash-Safe, Concurrent Transaction
System](https://pdos.csail.mit.edu/papers/mtheng-meng.pdf)". The framework has
evolved in several ways since then. See the tag `osdi21` for the version used
there.

Perennial 1 is described in our SOSP paper, "[Verifying concurrent, crash-safe
systems with Perennial](https://www.chajed.io/papers/perennial:sosp2019.pdf)".
The actual codebase was quite different at the time of this paper; it notably
used a shallow embedding of Goose and does not have the same program logic. See
the tag `sosp2019` for this version of Perennial.
