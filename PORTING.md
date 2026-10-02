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
  `state * global_state` pair becomes a single iris-lean `State`.
* **Iris/stdpp substrate.** iris-lean provides the BI, proof mode, invariants,
  ghost maps, later credits and the WP. stdpp-style helpers that iris-lean lacks
  live in `Perennial/Std`.
  * Finite maps are `Perennial.gmap K V` (`Perennial/Std/GMap.lean`): finite
    partial functions, extensional so `=` works as in stdpp, needing only
    `DecidableEq K`. `gset K = gmap K Unit`. It is an iris-lean
    `LawfulFiniteMap`, so iris-lean's `ghost_map`/`gen_heap` apply.
  * Machine words are `BitVec n` (`w64 = BitVec 64`, ...). `uint.Z x` is
    `(x.toNat : Int)` and `sint.Z x` is `x.toInt`. Arithmetic side conditions
    are discharged with `omega`, `bv_omega` and `bv_decide` in place of
    coqutil's `word`.
  * `go_string` (Rocq `byte_string`) is `List w8`.
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

See `PORTING_STATUS.md`.

## Conventions for porters

* Keep Rocq identifiers (`wp_load`, `is_Mutex`, `own_slice`) so a Rocq name can
  be found with grep. Rename only when a name is not legal Lean (for example the
  `'` suffix and `ⁱᵐᵖˡ` work, but `go.type` is the namespaced `go.type`).
* Everything lives in `namespace Perennial`. Rocq `Module foo` becomes
  `namespace foo`.
* Files do not use the Lean `module` system (no `public import`).
* Rocq `Admitted` becomes `sorry`, with a comment `-- Rocq: Admitted` when the
  Rocq source was also admitted. A proof that is merely not ported yet is
  `sorry` with `-- TODO(port)`. Never add `axiom`s except where Rocq has one.
* Notation: `#x` is `into_val x`; `m !! k`, `<[k := v]> m`, `{[k := v]}` work on
  both `gmap` and `List` (on lists they are `l[i]?` and `l.set i v`); stdpp's
  set-valued `dom m` is `domSet m`; `go!"abc"` is a `go_string` literal; `l +ₗ i` is location
  offset.
* Equality on GooseLang syntax and `go.type` is decided classically
  (`noncomputable instance`), as Rocq admits these instances.
* Check a file with `lake build Perennial.Path.To.Module` (from the repo root).
