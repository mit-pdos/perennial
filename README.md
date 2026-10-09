# Perennial

Perennial's goose framework and program proofs, in Lean 4 on top of
[iris-lean](https://github.com/leanprover-community/iris-lean). This branch
(`lean`) is the primary branch. It covers Go programs translated by goose,
without crash/recovery reasoning.

Guides: [`docs/PERENNIAL_PROOF_TUTORIAL.md`](docs/PERENNIAL_PROOF_TUTORIAL.md),
[`docs/PERENNIAL_PROOF_REFERENCE.md`](docs/PERENNIAL_PROOF_REFERENCE.md),
[`docs/IRIS_PROOF_MODE.md`](docs/IRIS_PROOF_MODE.md).

## Design decisions

* **One library, `Perennial`.** Framework directories are UpperCamelCase
  (`Perennial/Golang/Theory/Slice.lean`); generated and proof directories
  follow Go package paths (`Perennial/Proof/github_com/tchajed/marshal.lean`).
* **No crash logic.** There is no crash program logic (`wpc`, staged
  invariants, recovery adequacy, `crash_borrow`): proofs reason about
  executions without crashes. GooseLang is an instance of iris-lean's
  `Language`, and proofs use iris-lean's `wp`, which has later credits and
  `numLatersPerStep`. The local and global state (`state × GlobalState`) form
  the single iris-lean `State`, `CfgState`.
* **Bounded-step layer and time receipts.** The trusted semantics `BaseStep`
  (and its iris-lean language `gooseRealEctxiLang`, `GooseLang/Lang.lean`)
  is unchanged, but the language instance used by the program logic is a
  separate step-bounded layer (`GooseLang/BoundedLang.lean`): its state adds a
  *fuel* of Go-instruction steps, and once the fuel is exhausted Go
  instructions stutter instead of stepping. This supports *time receipts*
  (Mével, Jourdan, Pottier, ESOP 2019; `GooseLang/Receipts.lean`): `⧗ n`/`⧖ n`,
  with `⧗ N ⊢ False` for the bound `N = receiptBound GF`.
  The bound is an *unspecified parameter*, not a constant: it is a field of the
  receipt ghost state `ReceiptGS GF` (part of `GooseGlobalGS`, hence of
  `HeapGS`), so downstream files, whose sections already assume `HeapGS`, need
  no new argument, and the language instance and its `PureExec`/`Atomic`
  instances do not depend on it. A proof that needs `N` to be small takes a
  premise (`wp_clock_incr` in `ProgramLogic/TimeReceiptsTest.lean` takes
  `receiptBound GF ≤ 2 ^ 64`). The
  adequacy theorems (`goose_adequacy N`, `goose_invariance N`, and the
  grove/disk ones) hold for every `N`: they allocate the receipt ghost state
  with `receiptBound GF = N` (a hypothesis of the WP premise `Hwp`, from which
  the client discharges the proof's premises about `N`) and are about real
  executions of *fewer than `N` steps*, an explicit hypothesis. See
  `docs/PERENNIAL_PROOF_REFERENCE.md`, "Time receipts".
* **Iris substrate.** iris-lean provides the BI, proof mode, invariants,
  ghost maps, later credits and the WP. General-purpose libraries that iris-lean
  lacks (finite maps and sets, machine words, list lemmas) live in
  `Perennial/Std`.
  * Finite maps are `Perennial.gmap K V` (`Perennial/Std/GMap.lean`): finite
    partial functions, extensional so `=` is equality of bindings, needing only
    `DecidableEq K`. `gset K = gmap K Unit`. It is an iris-lean
    `LawfulFiniteMap`, so iris-lean's `ghost_map`/`gen_heap` apply.
  * Machine words are `BitVec n` (`w64 = BitVec 64`, ...). `uint.Z x` is
    `(x.toNat : Int)` and `sint.Z x` is `x.toInt`. Arithmetic side conditions
    are discharged with `word`, `omega` and `bv_omega`. Do not use `bv_decide`/`native_decide`: they trust
    native code (`Lean.ofReduceBool`); prove bitwise facts via `toNat`.
  * `GoString` is `List w8`.
* **64-bit platform.** The Go semantics assumes a 64-bit platform: the
  word-sized types `int`, `uint` and `uintptr` are 64-bit (values `w64`).
  `uintptr` (`go.UintptrSemantics`, `Perennial/Golang/Defn/Predeclared.lean`)
  is an integer type like `uint64`. Pointer/`unsafe.Pointer` to/from `uintptr`
  conversions are not modelled: they are stuck.
* **Generated code comes from goose.** The translator in `goose/` emits
  `Perennial/Code/**` and `Perennial/GeneratedProof/**`; regenerate with
  `etc/update-goose-new.py` rather than editing them by hand.

## Layering (bottom up)

| Directory                    | Contents                                                    |
|------------------------------|-------------------------------------------------------------|
| `Perennial/Std`              | general libraries (gmap, words, lists, bytes)               |
| `Perennial/Algebra`          | cameras and ghost-state algebra                             |
| `Perennial/GooseLang`        | GooseLang: semantics, lifting, bounded-step layer, receipts |
| `Perennial/GooseLang/Ffi`    | grove and disk FFIs                                         |
| `Perennial/Golang/Defn`      | the Go model                                                |
| `Perennial/Golang/Theory`    | its program logic and spec lemmas                           |
| `Perennial/Ghost`            | ghost-state libraries                                       |
| `Perennial/TrustedCode`      | trusted (hand-written) models of Go code                    |
| `Perennial/Code`             | GooseLang code (generated by goose)                         |
| `Perennial/GeneratedProof`   | generated proof boilerplate (generated by proofgen)         |
| `Perennial/Proof`            | hand-written program proofs                                 |

## Status

Run `etc/lean-ci.sh` + `etc/lean-audit.py` for the build and soundness audit
(`sorry` roots, axioms and `opaque`s).

## Conventions

* Follow the naming of the surrounding code (`wp_load`, `isMutex`, `ownSlice`).
  Quote names that are not legal Lean with «» (e.g. `Mutex.impl`, `«unsafe»`).
* Sealing: `def foo_def`, `@[irreducible] def foo := foo_def`,
  `theorem foo_unseal : foo = foo_def`. `Global Opaque` is `attribute [irreducible]`.
* GooseLang code notation (`Perennial/GooseLang/Notation.lean`): `λ: "x", e`,
  `let: "x" := e1 in e2`, `e1 ;; e2`, `if: c then a else b`, `rec: "f" "x" := e`,
  Go operators `e1 +⟨t⟩ e2` etc. Method calls are `rcvr @!! T @!! m`.
* Everything lives in `namespace Perennial`.
* Files do not use the Lean `module` system (no `public import`).
* An unfinished proof is `sorry`, with a comment saying what is missing if it
  is not obvious. Do not add new `axiom`s without discussing it first.
* Notation: `#x` is `intoVal x`; `m !! k`, `<[k := v]> m`, `{[k := v]}` work on
  both `gmap` and `List` (on lists they are `l[i]?` and `l.set i v`); the
  set-valued domain of a map is `domSet m`; `go!"abc"` is a `GoString` literal; `l +ₗ i` is location
  offset.
* Equality on GooseLang syntax and `go.GoType` is decided classically
  (`noncomputable instance`).
* `FfiSyntax` requires `Pos.Countable` of `ffi_opcode`/`ffi_val`, and
  `Loc`, `GoSlice`, `val`, `Expr`, `GoFunc`, `GoInterface`, `go.GoType`, ... are
  `Pos.Countable` (`Perennial/GooseLang/Countable.lean`, via an injection into
  `GenTree`), so ghost state can store values containing code.
* Check a file with `lake build Perennial.Path.To.Module` (from the repo root).
