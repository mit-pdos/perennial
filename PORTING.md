# Porting Perennial (new goose) to Lean

This branch is a port of the *new goose* part of Perennial from Rocq to Lean 4,
built on [iris-lean](https://github.com/leanprover-community/iris-lean). The
Rocq sources live on `master`: everything under `new/`, plus the pieces of
`src/` that `new/` imports. Old Perennial (old goose, crash/recovery
reasoning, `program_proof/`) is out of scope.

## Design decisions

* **One library, `Perennial`.** Rocq's two logical roots (`Perennial` = `src/`,
  `New` = `new/`) are merged into one Lean library. Directory names become
  UpperCamelCase (`new/golang/theory/slice.v` ->
  `Perennial/Golang/Theory/Slice.lean`).
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
* **64-bit platform.** As in Rocq, the Go semantics assumes a 64-bit platform: the
  word-sized types `int`, `uint` and `uintptr` are 64-bit (values `w64`).
  `uintptr` has semantics only in Lean (`go.UintptrSemantics`,
  `Perennial/Golang/Defn/Predeclared.lean`; Rocq declares only the type name). It
  is an integer type like `uint64`. Pointer/`unsafe.Pointer` to/from `uintptr`
  conversions are not modelled: they are stuck.
* **Generated code is regenerated, not translated.** `new/code` and
  `new/generatedproof` come from goose. `goose/` here carries a Lean backend
  that emits `Perennial/Code/**` and `Perennial/GeneratedProof/**`.

## Layering (bottom up)

| Lean                         | Rocq source                                         |
|------------------------------|-----------------------------------------------------|
| `Perennial/Std`              | stdpp gaps, `src/Helpers/*` (words, lists, bytes)    |
| `Perennial/Algebra`          | `src/algebra`, `src/iris_lib` (only what new uses)  |
| `Perennial/GooseLang`        | `src/goose_lang/{lang,lifting,ipersist,...}`        |
| `Perennial/GooseLang/Ffi`    | `src/goose_lang/ffi/{grove_ffi,disk_ffi}`           |
| `Perennial/Golang/Defn`      | `new/golang/defn*`                                  |
| `Perennial/Golang/Theory`    | `new/golang/theory*`                                |
| `Perennial/Ghost`            | `new/ghost`                                         |
| `Perennial/TrustedCode`      | `new/trusted_code`                                  |
| `Perennial/Code`             | `new/code` (generated)                              |
| `Perennial/GeneratedProof`   | `new/generatedproof` (generated)                    |
| `Perennial/Proof`            | `new/proof`, `new/manualproof`                      |

## Status

Run `etc/lean-port-status.py --rocq <master checkout>` for per-area file, line and sorry counts. See also `etc/fidelity-review.md`.

## Conventions for porters

* Keep Rocq identifiers (`wp_load`, `isMutex`, `ownSlice`) so a Rocq name can
  be found with grep. Rename only when a name is not legal Lean; quote with «» when
  possible (e.g. `Mutex.impl`, `«unsafe»`).
* Sealing: `def foo_def`, `@[irreducible] def foo := foo_def`,
  `theorem foo_unseal : foo = foo_def`. `Global Opaque` is `attribute [irreducible]`.
* GooseLang code notation (`Perennial/GooseLang/Notation.lean`): `λ: "x", e`,
  `let: "x" := e1 in e2`, `e1 ;; e2`, `if: c then a else b`, `rec: "f" "x" := e`,
  Go operators `e1 +⟨t⟩ e2` etc. Method calls are `rcvr @!! T @!! m`.
* Everything lives in `namespace Perennial`. Rocq `Module foo` becomes
  `namespace foo`.
* Files do not use the Lean `module` system (no `public import`).
* Rocq `Admitted` becomes `sorry`, with a comment `-- Rocq: Admitted` when the
  Rocq source was also admitted. A proof that is merely not ported yet is
  `sorry` with `-- TODO(port)`. Never add `axiom`s except where Rocq has one.
* Notation: `#x` is `intoVal x`; `m !! k`, `<[k := v]> m`, `{[k := v]}` work on
  both `gmap` and `List` (on lists they are `l[i]?` and `l.set i v`); stdpp's
  set-valued `dom m` is `domSet m`; `go!"abc"` is a `GoString` literal; `l +ₗ i` is location
  offset.
* Equality on GooseLang syntax and `go.GoType` is decided classically
  (`noncomputable instance`), as Rocq admits these instances.
* As in Rocq, `FfiSyntax` requires `Pos.Countable` of `ffi_opcode`/`ffi_val`, and
  `Loc`, `GoSlice`, `val`, `Expr`, `GoFunc`, `GoInterface`, `go.GoType`, ... are
  `Pos.Countable` (`Perennial/GooseLang/Countable.lean`, via an injection into
  `GenTree`), so ghost state can store values containing code.
* Check a file with `lake build Perennial.Path.To.Module` (from the repo root).
