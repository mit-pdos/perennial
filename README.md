# Perennial (new goose) in Lean

Perennial's new-goose framework and program proofs, in Lean 4 on top of
[iris-lean](https://github.com/leanprover-community/iris-lean). This branch
(`lean`) is the primary branch. The development began as a translation of the
Rocq code on `master` (`new/` and the parts of `src/` it uses). That translation
is finished, and the Rocq code is no longer a reference. Old Perennial (old
goose, crash/recovery reasoning, `program_proof/`) is not included.

Guides: [`docs/PERENNIAL_PROOF_TUTORIAL.md`](docs/PERENNIAL_PROOF_TUTORIAL.md),
[`docs/PERENNIAL_PROOF_REFERENCE.md`](docs/PERENNIAL_PROOF_REFERENCE.md),
[`docs/IRIS_PROOF_MODE.md`](docs/IRIS_PROOF_MODE.md).

## Do not consult the Rocq sources

The Rocq code on `master` is frozen and will drift out of date. Do not read it,
diff against it, or use it to decide what a definition or spec should be:

* The Lean statement is authoritative. To improve a spec or prove a `sorry`,
  work from the Go code and the Lean development, not from what Rocq did.
* Comments of the form `-- Rocq: Admitted`, `(Rocq: ...)`, "Rocq `foo`" or
  "Lean deviations from Rocq" are historical notes from the translation. They say
  where something came from, not what it must be; there is no need to check
  them against `master`, and they can be dropped when the code around them
  changes.

## Design decisions

* **One library, `Perennial`.** Framework directories are UpperCamelCase
  (`Perennial/Golang/Theory/Slice.lean`); generated and proof directories
  follow Go package paths (`Perennial/Proof/go_etcd_io/raft/v3.lean`).
* **No crash logic.** Perennial's crash program logic (`wpc`, staged
  invariants, `fupd_level`, recovery adequacy, `crash_borrow`) is used by new
  goose only for disk/crash examples, so it is dropped. GooseLang is an
  instance of iris-lean's `Language`, and proofs use iris-lean's `wp`, which
  already has later credits and `numLatersPerStep`. Perennial's
  `state * GlobalState` pair becomes a single iris-lean `State`.
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
  premise (`idutil.Generator.wp_Next` takes `receiptBound GF ≤ 2 ^ 48`). The
  adequacy theorems (`goose_adequacy N`, `goose_invariance N`, and the
  grove/disk ones) hold for every `N`: they allocate the receipt ghost state
  with `receiptBound GF = N` (a hypothesis of the WP premise `Hwp`, from which
  the client discharges the proof's premises about `N`) and are about real
  executions of *fewer than `N` steps*, an explicit hypothesis. See
  `docs/PERENNIAL_PROOF_REFERENCE.md`, "Time receipts".
* **Iris/stdpp substrate.** iris-lean provides the BI, proof mode, invariants,
  ghost maps, later credits and the WP. stdpp-style helpers that iris-lean lacks
  live in `Perennial/Std`.
  * Finite maps are `Perennial.gmap K V` (`Perennial/Std/GMap.lean`): finite
    partial functions, extensional so `=` works as in stdpp, needing only
    `DecidableEq K`. `gset K = gmap K Unit`. It is an iris-lean
    `LawfulFiniteMap`, so iris-lean's `ghost_map`/`gen_heap` apply.
  * Machine words are `BitVec n` (`w64 = BitVec 64`, ...). `uint.Z x` is
    `(x.toNat : Int)` and `sint.Z x` is `x.toInt`. Arithmetic side conditions
    are discharged with `word`, `omega` and `bv_omega` in place of
    coqutil's `word`. Do not use `bv_decide`/`native_decide`: they trust
    native code (`Lean.ofReduceBool`); prove bitwise facts via `toNat`.
  * `GoString` (Rocq `byte_string`) is `List w8`.
* **64-bit platform.** The Go semantics assumes a 64-bit platform: the
  word-sized types `int`, `uint` and `uintptr` are 64-bit (values `w64`).
  `uintptr` (`go.UintptrSemantics`, `Perennial/Golang/Defn/Predeclared.lean`)
  is an integer type like `uint64`. Pointer/`unsafe.Pointer` to/from `uintptr`
  conversions are not modelled: they are stuck.
* **Generated code comes from goose.** `goose/` carries a Lean backend that
  emits `Perennial/Code/**` and `Perennial/GeneratedProof/**`; regenerate with
  `etc/update-goose-new.py --lean` rather than editing them by hand.

## Layering (bottom up)

| Directory                    | Contents                                                    |
|------------------------------|-------------------------------------------------------------|
| `Perennial/Std`              | stdpp-style helpers (gmap, words, lists, bytes)             |
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
* An unfinished proof is `sorry` with a comment saying what is missing (existing
  `-- Rocq: Admitted` / `-- TODO(port)` markers mean the same: not proved yet).
  Do not add new `axiom`s without discussing it first.
* Notation: `#x` is `intoVal x`; `m !! k`, `<[k := v]> m`, `{[k := v]}` work on
  both `gmap` and `List` (on lists they are `l[i]?` and `l.set i v`); stdpp's
  set-valued `dom m` is `domSet m`; `go!"abc"` is a `GoString` literal; `l +ₗ i` is location
  offset.
* Equality on GooseLang syntax and `go.GoType` is decided classically
  (`noncomputable instance`).
* `FfiSyntax` requires `Pos.Countable` of `ffi_opcode`/`ffi_val`, and
  `Loc`, `GoSlice`, `val`, `Expr`, `GoFunc`, `GoInterface`, `go.GoType`, ... are
  `Pos.Countable` (`Perennial/GooseLang/Countable.lean`, via an injection into
  `GenTree`), so ghost state can store values containing code.
* Check a file with `lake build Perennial.Path.To.Module` (from the repo root).
