# Perennial Proof Tutorial (Lean)

A guide to writing program proofs for Go code in the Lean 4 port of Perennial
(new goose, on top of [iris-lean](https://github.com/leanprover-community/iris-lean)).
It follows the structure of the Rocq tutorial (`new/proof/PERENNIAL_PROOF_TUTORIAL.md`
on `master`) but describes how things work in this port.

* Every Lean block below is copied verbatim from
  [`docs/TutorialExamples.lean`](TutorialExamples.lean) (between the
  `-- ANCHOR: name` / `-- ANCHOR_END: name` comments). That file is checked with

  ```
  lake env lean docs/TutorialExamples.lean
  ```

  from the repository root (it imports built modules, so `lake build` them
  first). If you change an example, change it in both places.
* Tactic details and spec lemmas: [`PERENNIAL_PROOF_REFERENCE.md`](PERENNIAL_PROOF_REFERENCE.md).
* The Iris proof mode (`iintro`, `icases`, ...) and a Rocq → Lean translation
  table: [`IRIS_PROOF_MODE.md`](IRIS_PROOF_MODE.md).
* Design decisions and porting conventions: [`../PORTING.md`](../PORTING.md).

## 1. Project layout

| Directory | Contents |
|:--|:--|
| `Perennial/Std` | stdpp-style helpers: `gmap`, words (`w64 = BitVec 64`), list lemmas, `word`/`len` tactics |
| `Perennial/Algebra`, `Perennial/Ghost` | cameras and ghost-state libraries (`ghost_var`, `ghost_map`, `mono_list`, ...) |
| `Perennial/GooseLang` | the GooseLang language, its lifting lemmas (`wp_fork`, `wp_cmpxchg_suc`, ...) |
| `Perennial/Golang/Defn` | the Go model: types, instructions, `@!` notation |
| `Perennial/Golang/Theory` | the program logic for Go and the proof tactics (`Auto.lean`, `ProofMode.lean`, `Mem.lean`, `Slice.lean`, `Map.lean`, `Loop.lean`, `Pkg.lean`, ...) |
| `Perennial/TrustedCode` | hand-written models of trusted Go code (e.g. `sync.Mutex`) |
| `Perennial/Code/**` | **generated**: GooseLang translation of Go packages |
| `Perennial/GeneratedProof/**` | **generated**: per-package proof boilerplate (struct points-to instances, ...) |
| `Perennial/Proof/**` | hand-written proofs (`Perennial/Proof/sync_proof/mutex.lean`, `Perennial/Proof/sort_proof/search.lean`, ...) |
| `goose/` | the goose translator, with the Lean backend (`goose -lean`, `proofgen -lean`) |
| `etc/update-goose-new.py` | runs goose and proofgen over all supported packages |

A Go package with import path `github.com/mit-pdos/perennial/goose/testdata/examples/unittest`
lives in `Perennial/Code/github_com/mit_pdos/perennial/goose/testdata/examples/unittest.lean`
(and the same path under `GeneratedProof/`), in the Lean namespace
`Perennial.github_com.mit_pdos.perennial.goose.testdata.examples.unittest`, and
its package name is `pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest`.
Standard-library packages are short: `Perennial/Code/sync.lean`, namespace
`Perennial.sync`, package `pkg_id.sync`. Proofs mirror the Rocq layout:
`new/proof/sync_proof/mutex.v` becomes `Perennial/Proof/sync_proof/mutex.lean`.

Check a single file with `lake build Perennial.Proof.sync_proof.mutex` (module
name = path with `.` for `/`).

## 2. Generating code with goose

Never edit `Perennial/Code` or `Perennial/GeneratedProof` by hand; regenerate
them:

```
etc/update-goose-new.py --lean --compile --std-lib --goose-examples
etc/update-goose-new.py --lean --etcd-raft ../etcd-raft     # an external project
etc/update-goose-new.py --lean --all                        # everything found in ../<proj>
```

`--lean` selects the Lean backend (without it the script writes the Rocq
`new/code`, `new/generatedproof`); `--compile` first runs
`go install ./goose/cmd/goose ./goose/cmd/proofgen`; `-n` prints the commands.
For each package the script runs `goose -lean -out Perennial/Code -configdir Perennial/Code`
and `proofgen -lean -out Perennial/GeneratedProof -configdir Perennial/Code`.

**Configuration.** A `<pkg>.toml` next to the generated file (e.g.
`Perennial/Code/sort.toml`, `Perennial/Code/sync.toml`) selects what is
translated. Each key is a list of glob patterns applied left to right, starting
from the empty set (`"*"` is a wildcard, `"!p"` removes matches):

```toml
# Perennial/Code/sort.toml
translate = ["Search", "SearchInts", "Find", "*Hint", "xorshift", "xorshift.*"]
imports = ["!*"]
```

* `translate`: declarations to translate (default: all);
* `imports`: imports to keep (default: all);
* `trusted`: declarations with a hand-written model in `Perennial/TrustedCode`
  (`sync.toml` trusts `"Mutex", "Mutex.*"`, which really have data races);
* every other declaration is *axiomatized*: its name and type are emitted,
  without a body. (`sync.toml` also has an `axiomatize = [...]` list; goose does
  not read that key, it documents the intent.)
* `trust_proofgen = true` makes proofgen emit admitted (`sorry`) instances.

**What is generated.** For each package, `Perennial/Code/<pkg>.lean` contains

* `pkg_id.<pkg> : go_string` and a `PkgInfo` instance (the imported packages);
* for every function `F`, its name `def F : go_string := go!"pkg.F"` and its
  body `def «Fⁱᵐᵖˡ» : val` (methods are `«T__mⁱᵐᵖˡ»`);
* types (`def S : go.type`), and the struct value types `S.t` with fields `a'`, `b'`, ...;
* `initialize'`, the package initialization function;
* `class Assumptions`: the facts a proof may assume about the package, such as
  `FuncUnfold F [] «Fⁱᵐᵖˡ»` (calling `F` runs its body) and the struct
  field-access semantics. Proofs take `[package_sem : <pkg>.Assumptions]`.

`Perennial/GeneratedProof/<pkg>.lean` contains, for each struct, the typed
points-to `TypedPointsto S.t` (one named conjunct per field), `IntoValTyped`,
and the `AccessStrict` instances that let `wp_load`/`wp_store` work on a single
field of a struct points-to.

## 3. A proof file

A proof file imports the generated proof and the proofs of its dependencies, and
opens a section with the standard variables. For the examples we use the goose
unit-test package (its proof file already defines its `IsPkgInit` instance):

```lean
import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.unittest
import Perennial.Proof.sync_proof.mutex
```

```lean
section tutorial
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics] [package_sem : unittest.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest
```

The unit-test package imports `github.com/goose-lang/primitive/disk`, so its
FFI is fixed to the disk FFI (global instances from `Perennial.Proof.DiskPrelude`)
and the section does not bind it. Other packages are generic in the FFI and also
bind `[ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]`,
as in `Perennial/Proof/sync_proof/mutex.lean`. Proofs that need ghost state add
`[allG GF]` (section 10).

## 4. Writing a specification

A specification is a *Texan triple*

```
{{ P }} e {{ (x : T) ..., RET v; Q }}
```

which means `⊢ ∀ Φ, P -∗ ▷ (∀ x ..., Q -∗ Φ v) -∗ WP e {{ Φ }}`. The binders
before `RET` are optional (`{{ RET #(); True }}`).

* A call of the function `F` with arguments `x`, `y` is
  `(App (App (Val (@! F)) (Val #x)) (Val #y))`; `@! F` is the function value
  `#(functions F [])`.
* A method call `r.m(x)` is `(App (Val (r @!! T @!! go!"m")) (Val #x))`, e.g.
  `(App (Val (m @!! go.type.PointerType Mutex @!! go!"Lock")) (Val #()))`.
* `#x` turns a Lean value (`w64`, `w8`, `Bool`, `loc`, `slice.t`, a struct `S.t`,
  `go_string`, `()`, ...) into a GooseLang `val`.
* Multiple return values are a pair: `RET (PairV #a #b)`.
* The precondition starts with `is_pkg_init (PROP := IProp GF) pkg`; the
  `(PROP := ...)` is needed when nothing else in the precondition fixes the
  logic (write it always, as the ported proofs do).

The first example: `wp_start` introduces the continuation `HΦ` and the
precondition (moving `is_pkg_init` facts to the intuitionistic context) and
unfolds the function; `wp_auto` runs the straight-line code; `wp_end` applies
`HΦ` and tries to close the rest.

```lean
/-- `func conditionalReturn(x bool) uint64 { if x { return 0 }; return 1 }` -/
theorem wp_conditionalReturn' (x : Bool) :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! conditionalReturn)) (Val #x))
    {{ (r : w64), RET #r; ⌜r = if x then W64 0 else W64 1⌝ }} := by
  wp_start
  wp_auto
  cases x
  · wp_auto
    wp_end
  · wp_auto
    wp_end
```

`wp_if_destruct` splits on the condition of the `if:` at the head of the
program (here the Boolean variable `x`); the case hypothesis is called `Hif`:

```lean
/-- The same proof with `wp_if_destruct`, which splits on the condition of the
`if:` at the head of the program. -/
theorem wp_conditionalReturn'' (x : Bool) :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! conditionalReturn)) (Val #x))
    {{ (r : w64), RET #r; ⌜r = if x then W64 0 else W64 1⌝ }} := by
  wp_start
  wp_auto
  wp_if_destruct
  · wp_end
  · wp_end
```

Local variables become heap cells: `wp_auto` handles allocations, loads and
stores of locals (naming the cell of Go variable `p` as `p_ptr` with points-to
hypothesis `p`), and drops points-to facts of locals that are dead.

```lean
/-- `func usePtr() { p := new(uint64); *p = 1; x := *p; *p = x }` -/
theorem wp_usePtr' :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! usePtr)) (Val #()))
    {{ RET #(); True }} := by
  wp_start
  wp_auto
  wp_end
```

## 5. Calling other functions: `wp_apply`

`wp_apply lem $$ spats as pats` finds the call in the goal, applies the spec,
proves its `is_pkg_init` premises, introduces the postcondition with the
iris-lean intro patterns `pats` and runs `wp_auto`. (`with` is a synonym of
`as`; `--no-auto` skips the `wp_auto`.)

```lean
/-- `func returnTwo(p []byte) (uint64, uint64) { return 0, 0 }`.
Multiple return values are a `PairV`. -/
theorem wp_returnTwo' (p : slice.t) :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! returnTwo)) (Val #p))
    {{ RET (PairV #(W64 0) #(W64 0)); True }} := by
  wp_start
  wp_auto
  wp_end

/-- `func returnTwoWrapper(data []byte) (uint64, uint64)` calls `returnTwo`. -/
theorem wp_returnTwoWrapper' (data : slice.t) :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! returnTwoWrapper)) (Val #data))
    {{ RET (PairV #(W64 0) #(W64 0)); True }} := by
  wp_start
  wp_auto
  wp_apply wp_returnTwo'
  wp_end
```

More `wp_apply` forms used in the examples below:

```
wp_apply sync.wp_Mutex__Lock $$ [$Hm] as ⟨Hlocked, HR⟩       -- frame Hm, destruct the post
wp_apply (wp_map_make1 (K := w64) (V := slice.t)) as %m Hm    -- %m: the return binder
wp_apply wp_load_slice_index s (sint.Z i) vs _ x Hi.1 $$ [Hs] with Hs   -- explicit arguments
```

## 6. The heap and structs

Points-to notation: `l ↦ v` (full), `l ↦{dq} v`, `l ↦□ v` (persistent);
slices `s ↦* vs`, `s ↦*{dq} vs`; maps `m ↦$ m'`. A struct field address is
`l.[S.t, go!"f"]` (note `go!"f"`, not `"f"`). `wp_auto` loads and stores single
fields of a struct points-to `s ↦ v` directly, through the generated
`AccessStrict` instances:

```lean
/-- `func (s *S) writeB(two TwoInts) { s.b = two }` -/
theorem wp_S__writeB' (s : loc) (v : S.t) (two : TwoInts.t) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ s ↦ v }}
      (App (Val (s @!! go.type.PointerType S @!! go!"writeB")) (Val #two))
    {{ RET #(); s ↦ ({ v with b' := two } : S.t) }} := by
  wp_start as Hs
  wp_auto
  iapply HΦ $$ Hs
```

An anonymous allocation (`&S{...}`, not bound by a Go variable) is not done by
`wp_auto`; use `wp_alloc l as H` (or `wp_alloc_auto`). `iStructNamed H` splits a
struct points-to into its fields:

```lean
/-- `func NewS() *S { return &S{a: 2, b: TwoInts{x: 1, y: 2}, c: true} }`.
The anonymous allocation `&S{..}` is done with `wp_alloc`; `iStructNamed`
splits the struct points-to into one points-to per field. -/
theorem wp_NewS' :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! NewS)) (Val #()))
    {{ (s : loc), RET #s; s.[S.t, go!"a"] ↦ W64 2 ∗ s.[S.t, go!"c"] ↦ true }} := by
  wp_start
  wp_alloc s as Hs
  iStructNamed Hs
  wp_end
```

## 7. Representation predicates and `iNamed`

Name the conjuncts of a predicate with `"name" ∷ P`; `iNamed H` introduces the
existentials and names the conjuncts. The names are iris-lean cases patterns
written as strings: `"H"`, `"#H"` (intuitionistic), `"%H"` (Lean context).

```lean
/-- A representation predicate with named conjuncts (`"name" ∷ P`). The names
are iris-lean cases patterns: `"%Hbound"` goes to the Lean context. -/
def own_bounded (l : loc) : IProp GF :=
  iprop(∃ n : w64,
    "Hv" ∷ (l ↦ n : IProp GF) ∗
    "%Hbound" ∷ ⌜uint.Z n < 100⌝)

theorem own_bounded_get (l : loc) :
    own_bounded (GF := GF) l ⊢ ∃ n : w64, l ↦ n ∗ ⌜uint.Z n < 200⌝ := by
  iintro H
  iNamed H            -- introduces `n`, `Hv`, and `Hbound : uint.Z n < 100`
  iexists n
  iframe Hv
  ipureintro; omega
```

Seal definitions that clients should not unfold (`@[irreducible] def foo :=
foo_def` with `theorem foo_unseal : foo = foo_def`) and unfold them in proofs
with `simp only [foo_unseal, foo_def]` (see `is_Mutex` in
`Perennial/Proof/sync_proof/mutex.lean`).

## 8. Loops, slices

For a loop, state the invariant with `ihave HI : P $$ [hyps]` (Rocq `iAssert`):
the first goal proves `P` from `hyps`, then `HI` is available. `wp_for HI`
applies the loop rule (the whole remaining context becomes the loop invariant)
and destructs `HI` with `iNamed`. The loop condition is a `decide`: split it with
`wp_if_destruct`. In the body, `wp_for_post` handles the end of an iteration
(fall-through, `continue`, `break`, `return`); then re-establish the invariant.

```lean
/-- The sum of a list of words (wrapping on overflow, like Go's `+`). -/
def sum_w64 (xs : List w64) : w64 := xs.foldl (· + ·) 0

theorem sum_w64_take_succ (xs : List w64) (n : Nat) (x : w64) (h : xs[n]? = some x) :
    sum_w64 (xs.take (n + 1)) = sum_w64 (xs.take n) + x := by
  unfold sum_w64
  rw [List.take_add_one, List.foldl_append, h]
  rfl
```

````lean
/-- `func intSliceLoop(xs []uint64) uint64`:
```go
var sum uint64
for i := 0; i < len(xs); i++ { sum += xs[i] }
return sum
``` -/
theorem wp_intSliceLoop' (s : slice.t) (vs : List w64) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ s ↦* vs }}
      (App (Val (@! intSliceLoop)) (Val #s))
    {{ RET #(sum_w64 vs); s ↦* vs }} := by
  wp_start as Hs
  wp_auto
  ihave %Hlen := own_slice_len _ _ _ $$ Hs
  -- the loop invariant
  ihave HI : (∃ i : w64,
      "i" ∷ i_ptr ↦ i ∗
      "sum" ∷ sum_ptr ↦ sum_w64 (vs.take (sint.nat i)) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z s.len⌝ : IProp GF) $$ [i sum]
  · iexists W64 0
    rw [show sum_w64 (vs.take (sint.nat (W64 0))) = zero_val w64 from rfl]
    iframe
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · -- loop body
    simp only [Hi.1, Hif, and_self, ↓reduceIte]
    list_elem vs (sint.nat i) as x
    wp_apply wp_load_slice_index s (sint.Z i) vs _ x Hi.1 $$ [Hs] with Hs
    · iframe; ipureintro; exact Hx_lookup
    wp_for_post
    iframe
    iexists i + W64 1
    rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word,
      sum_w64_take_succ vs _ x Hx_lookup]
    iframe
    ipureintro; word
  · -- loop exit: `i = len(xs)`
    rw [show sint.nat i = vs.length by word, List.take_length]
    wp_end
````

Things to note:

* `own_slice_len` gives the length fact (`vs.length = sint.nat s.len`);
  `ihave %H := lem $$ Hs` puts it in the Lean context without consuming `Hs`.
* Slice indexing has a bounds check (`if 0 ≤ i ∧ i < len then ... else Panic`);
  discharge it with `simp only [...]`.
* `list_elem vs n as x` gives `x` and `Hx_lookup : vs[n]? = some x` (proving the
  bound with `len`).
* `iframe` only cancels syntactically equal terms: `rw` the goal into shape first
  (the `rw [show ... from rfl]` and `rw [sum_w64_take_succ ...]` above).

## 9. Maps, goroutines, locks

Maps use `wp_map_make1`, `wp_map_insert`, `wp_map_lookup1`/`wp_map_lookup2`,
`wp_map_delete` (`Perennial/Golang/Theory/Map.lean`):

````lean
/-- ```go
func useMap() {
	m := make(map[uint64][]byte)
	m[1] = nil
	x, ok := m[2]
	if ok { return }
	m[3] = x
}
``` -/
theorem wp_useMap' :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! useMap)) (Val #()))
    {{ RET #(); True }} := by
  wp_start
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := slice.t)) as %m Hm
  wp_apply wp_map_insert $$ Hm as Hm
  wp_apply wp_map_lookup2 $$ Hm as Hm
  -- `ok` is `false` (key 2 is absent), so `wp_auto` took the fall-through branch
  wp_apply wp_map_insert $$ Hm as Hm
  wp_end
````

A `sync.Mutex` protects a lock invariant `R` (`sync.is_Mutex l R`, persistent):
`Lock` gives `own_Mutex l ∗ R`, `Unlock` takes them back. The precondition must
also have `is_pkg_init pkg_id.sync`. `wp_start as #Hm` moves both `is_pkg_init`
facts aside and destructs the rest (`is_Mutex`) with `#Hm`:

```lean
/-- `func DoSomeLocking(l *sync.Mutex) { l.Lock(); l.Unlock() }`, for any lock
invariant `R`. -/
theorem wp_DoSomeLocking' [sync.Assumptions] (l : loc) (R : IProp GF) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ is_pkg_init (PROP := IProp GF) pkg_id.sync ∗
        sync.is_Mutex l R }}
      (App (Val (@! DoSomeLocking)) (Val #l))
    {{ RET #(); True }} := by
  wp_start as #Hm
  wp_auto
  wp_apply sync.wp_Mutex__Lock $$ [$Hm] as ⟨Hlocked, HR⟩
  wp_apply sync.wp_Mutex__Unlock $$ [$Hm $Hlocked $HR]
  wp_end
```

A `go` statement is `Fork e`; `wp_fork` (`Perennial/GooseLang/Lifting.lean`)
asks for `WP e {{ True }}` for the new goroutine. Resources shared by both
goroutines must be persistent (`ipersist H` turns `l ↦ v` into `l ↦□ v`), or
protected by a lock created with `sync.init_Mutex`:

````lean
/-- ```go
func simpleSpawn() {
	l := new(sync.Mutex)
	v := new(uint64)
	go func() {
		l.Lock(); x := *v; if x > 0 { Skip() }; l.Unlock()
	}()
	l.Lock(); *v = 1; l.Unlock()
}
``` -/
theorem wp_simpleSpawn' [sync.Assumptions] :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ is_pkg_init (PROP := IProp GF) pkg_id.sync }}
      (App (Val (@! simpleSpawn)) (Val #()))
    {{ RET #(); True }} := by
  wp_start
  wp_auto
  -- both `new` allocations are bound to `$r0` by goose, so the mutex's location
  -- and points-to are inaccessible: name them (by position, then by type)
  rename_i mu_ptr
  irename : (mu_ptr ↦ zero_val Bool : IProp GF) => Hmu
  imod sync.init_Mutex iprop(∃ x : w64, «$r0_ptr» ↦ x) ⊤ mu_ptr $$ Hmu [«$r0»] with #Hlock
  · inext; iexists _; iexact «$r0»
  -- the local variables `l` and `v` are read by both goroutines
  ipersist l
  ipersist v
  wp_apply wp_fork $$ []
  · -- the spawned goroutine
    wp_auto
    wp_apply sync.wp_Mutex__Lock $$ [$Hlock] as ⟨Hlocked, ⟨%x, Hx⟩⟩
    wp_if_destruct
    · wp_func_call   -- `Skip()`: unfold the function and step through it
      wp_call
      wp_auto
      wp_apply sync.wp_Mutex__Unlock $$ [$Hlock $Hlocked Hx]
      · iexists _; iexact Hx
      itrivial
    · wp_apply sync.wp_Mutex__Unlock $$ [$Hlock $Hlocked Hx]
      · iexists _; iexact Hx
      itrivial
  -- the main goroutine
  wp_apply sync.wp_Mutex__Lock $$ [$Hlock] as ⟨Hlocked, ⟨%x, Hx⟩⟩
  wp_apply sync.wp_Mutex__Unlock $$ [$Hlock $Hlocked Hx]
  · iexists _; iexact Hx
  wp_end
````

## 10. Ghost state and invariants

Ghost state needs `[allG GF]` (one universal camera; no per-algebra `inG`
classes): `ghost_var`, `ghost_map`, `mono_list`, `saved_prop`, ... live in
`Perennial/Ghost`. Invariants are iris-lean's `inv N P`; `imod inv_alloc N E P $$ [..]`
allocates, `iinv H with pat Hclose` opens one around an atomic step, and
`imod Hclose $$ [..]` closes it.

```lean
/-- The invariant owns half of a ghost variable `γ` holding a counter; the
other half is held by a client. (An `abbrev`, so that `iexists`/`icases` see
through it; for a `def`, `unfold counter_inv` first.) -/
abbrev counter_inv (γ : GName) : IProp GF :=
  iprop(∃ n : Nat, ghost_var γ (1 : Qp).half n)

theorem counter_alloc (N : Namespace) (E : CoPset) :
    ⊢ |={E}=> ∃ γ, inv N (counter_inv γ) ∗ ghost_var γ (1 : Qp).half (0 : Nat) := by
  imod ghost_var_alloc (0 : Nat) with ⟨%γ, Hv⟩
  icases ghost_var_split γ (0 : Nat) (1 : Qp).half (1 : Qp).half $$ [Hv] with ⟨Hv1, Hv2⟩
  · rw [Qp.half_add_half]; iexact Hv
  imod inv_alloc N E (counter_inv γ) $$ [Hv1] with #Hinv
  · inext; iexists 0; iexact Hv1
  imodintro
  iexists γ
  iframe # ∗

theorem counter_incr (N : Namespace) (γ : GName) (n : Nat) :
    inv N (counter_inv γ) ∗ ghost_var γ (1 : Qp).half n ⊢
      |={⊤}=> ghost_var γ (1 : Qp).half (n + 1) := by
  iintro ⟨#Hinv, Hv⟩
  iinv Hinv with ⟨%m, >Hv'⟩ Hclose
  icombine Hv Hv' gives % ⟨_, Heq⟩
  subst Heq
  imod ghost_var_update_halves (n + 1) γ n n $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod Hclose $$ [Hv'] with _
  · inext; iexists _; iexact Hv'
  imodintro
  iexact Hv
```

In a program proof, `iinv` is used right before an atomic step: focus on it with
`wp_bind (Primitive1 _ _)` / `wp_bind (CmpXchg _ _ _)`, open the invariant,
`wp_apply_core` the atomic spec, close the invariant and `imodintro`. See
`wp_runtime_Semacquire` in `Perennial/Proof/sync_proof/sema.lean`. When the
invariant content is not timeless, eliminate the later with a later credit:
`wp_auto_lc 1` produces `Hlc1 : £ 1`, used as
`imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi` (see
`wp_Once__Do` in `Perennial/Proof/sync_proof/once.lean`).

## 11. Package initialization

`is_pkg_init pkg` asserts that the package was initialized (it includes
`is_pkg_init` of all its imports). Each package proof defines two instances and
proves `wp_initialize'`; `Perennial/Proof/sync_proof/base.lean` does this for
`sync`:

```lean
-- The two instances every package proof defines (here as `example`s, since
-- `sync_proof/base.lean` already declares them for `sync`):
example : IsPkgInit (IProp GF) pkg_id.sync := define_is_pkg_init iprop(True)
example : GetIsPkgInitWf (IProp GF) pkg_id.sync := build_get_is_pkg_init_wf

-- The initialization proof: run `package.init`, initialize the imported
-- packages in order, and conclude `is_pkg_init`.
example (get_is_pkg_init : go_string → IProp GF)
    (Hinit : get_is_pkg_init_prop pkg_id.sync get_is_pkg_init) :
    {{ own_initializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); own_initializing get_is_pkg_init ∗
        is_pkg_init (PROP := IProp GF) pkg_id.sync }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply internal.synctest.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hsynctest⟩
  wp_apply internal.race.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hrace⟩
  wp_apply sync.atomic.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hatomic⟩
  iframe Hown
  is_pkg_init_finish
```

* `define_is_pkg_init P` builds `IsPkgInit` with user part `P` (usually
  `iprop(True)`; Go globals and their invariants go here); the dependency part is
  computed from the package's imports, so their instances must exist.
* `wp_initialize'` initializes the imports in the order of `initialize'` in
  `Perennial/Code/<pkg>.lean`; `Hinit.2.1`, `Hinit.2.2.1`, ... are the
  imports' `get_is_pkg_init_prop` facts.
* In client specs, `wp_start` and `wp_apply` solve `is_pkg_init` premises
  automatically (`iPkgInit`), also when only a package importing it is
  available.

## 12. Arithmetic

* `word` (closes or fails): linear arithmetic on `uint.Z x`/`sint.Z x` with
  overflow; falls back to `bv_decide` for bitwise goals. `word_simp` is the
  non-terminal version.
* `omega` for plain `Nat`/`Int` goals; `uint.Z x` is `(x.toNat : Int)`,
  `sint.Z x` is `x.toInt`, `uint.nat`/`sint.nat` the `Nat` versions.
* `len` simplifies list lengths (`@[len]` simp set) and tries `word`; it never
  fails.
* `list_elem l i as x` obtains an element at an in-bounds index.

```lean
example (x : w64) (h : uint.Z x < 10) : uint.Z (x + W64 1) = uint.Z x + 1 := by word
example (x y : w64) (h : sint.Z x ≤ sint.Z y) (h' : 0 ≤ sint.Z x) : 0 ≤ sint.Z y := by word
example (l : List Nat) (n : Nat) (h : n ≤ l.length) : (l.take n ++ [3]).length = n + 1 := by len
example (l : List w64) (h : 2 < l.length) : True := by
  list_elem l 2 as y          -- `y : w64` and `Hy_lookup : l[2]? = some y`
  trivial
```

## 13. Common pitfalls

* **`|==> A ∗ B` is `(|==> A) ∗ B`.** In iris-lean `|==>`, `▷` and `□` bind
  tighter than `∗` (in Rocq `|==> A ∗ B` is `|==> (A ∗ B)`); the fancy update
  `|={E}=>` and the wands `==∗`, `={E}=∗` extend to the right. Write
  `|==> (A ∗ B)`.

  ```lean
  -- `|==>` (and `▷`, `□`) bind tighter than `∗`; `|={E}=>` extends to the right.
  example (P Q : IProp GF) : iprop(|==> P ∗ Q) = iprop((|==> P) ∗ Q) := rfl
  example (P Q : IProp GF) (E : CoPset) : iprop(|={E}=> P ∗ Q) = iprop(|={E}=> (P ∗ Q)) := rfl
  example (P Q : IProp GF) : iprop(▷ P ∗ Q) = iprop((▷ P) ∗ Q) := rfl
  ```

* **`set_option goose.wp.extras true`** (off by default, for backwards
  compatibility) enables extra automation in `wp_pures`/`wp_auto`: stored
  function literals become `#(func.mk ..)`, blocking package constants are
  unfolded, `match`es on constructors are reduced, slice composite literals are
  left for `wp_slice_literal`. Without it you sometimes need manual rewrites
  such as `rw [show ∀ b, (RecV BAnon BAnon b : val) = #(func.mk BAnon BAnon b) ...]`
  (see `once.lean`). Turn it on per declaration:

  ```lean
  set_option goose.wp.extras true in
  /-- `ifStmtInitialization` stores a function literal `f := func() uint64 {..}`
  in a local variable. -/
  theorem wp_ifStmtInitialization' (x : w64) :
      {{ is_pkg_init (PROP := IProp GF) pkg }}
        (App (Val (@! ifStmtInitialization)) (Val #x))
      {{ (r : w64), RET #r; True }} := by
    wp_start
    wp_auto      -- without `goose.wp.extras`, stuck at the store of `f`
    repeat' wp_if_destruct
    all_goals wp_end
  ```

* **Tactics fail instead of leaving a `sorry`.** All WP tactics fail when a term
  does not elaborate (they never insert a hidden `sorry`). Fix errors top-down: after a
  failed tactic Lean recovers with an admitted subgoal, and later tactics may
  behave differently than they will once the earlier error is fixed.

  ```lean
  /-- WP tactics fail (rather than leaving a `sorry`) when their argument does
  not elaborate. -/
  example (p : slice.t) :
      {{ is_pkg_init (PROP := IProp GF) pkg }}
        (App (Val (@! returnTwoWrapper)) (Val #p))
      {{ RET (PairV #(W64 0) #(W64 0)); True }} := by
    wp_start
    wp_auto
    fail_if_success wp_apply wp_returnTwo' p p    -- too many arguments: an error
    wp_apply wp_returnTwo'
    wp_end
  ```

* **`maxHeartbeats`.** Large loop proofs exceed the default 200000; put
  `set_option maxHeartbeats 400000 in` (or more; `pdqSort.lean` uses 4000000)
  before the theorem rather than splitting it artificially.
* **Inaccessible names.** goose binds temporaries as `$r0`, so `wp_auto` names
  their cells `«$r0_ptr»`/`«$r0»`, and a second `$r0` shadows the first
  (`$r0_ptr✝`). Name them with `rename_i x` (Lean) and `irename : (pat) => H`
  or `irename «$r0» => H` (Iris), as in the `simpleSpawn` example.
* **`def` vs `abbrev`.** `iexists`, `icases` and `iinv` do not unfold a `def`;
  `unfold` it first or make it an `abbrev`. `iNamed` unfolds the head
  definition unless it is `@[irreducible]`.
* **`_` vs `-` in patterns.** In iris-lean `_` keeps an anonymous hypothesis and
  `-` drops it (Rocq: `?` and `_`).
* **Ambiguous names after `open Iris.BI`.** E.g. `decide_true` is both
  `_root_.decide_true` and `BI.decide_true`; write `_root_.decide_true` in `simp`.
* **`wp_auto` fails when it makes no progress.** It stops at calls, `if:` on a
  non-literal, loops and anonymous allocations; use `wp_apply`, `wp_if_destruct`,
  `wp_for`, `wp_alloc`. `wp_func_call; wp_call` steps into a function without a
  spec.
* **`wp_apply` and lemmas without continuation.** If the applied spec closes the
  goal (e.g. a `panic` spec), use `wp_apply_core`.
* **Hypotheses that mention functions.** `wp_func_call` rewrites the first
  `#(functions ..)` in the goal; if a hypothesis mentions another function,
  `rw [func_unfold (f := F)]` instead (see `semantics_proof/panic.lean`).

## 14. Tactic summary

| Tactic | Use |
|:--|:--|
| `wp_start`, `wp_start as pat` | begin a triple proof (`HΦ`, precondition, unfold the call) |
| `wp_start_folded as pat` | same, without unfolding the function |
| `wp_auto`, `wp_auto_lc n` | pure steps, loads/stores/allocations of locals; `n` later credits `Hlc1..Hlcn` |
| `wp_apply lem $$ spats as pats` | apply a spec (`--no-auto`, `--lc n`) |
| `wp_apply_core lem $$ spats` | apply a spec, no automation |
| `wp_if_destruct` | case split on the head `if:` (`Hif`) |
| `wp_for`, `wp_for HI` | loop rule (`HI` destructed with `iNamed`) |
| `wp_for_post` | end of a loop iteration |
| `wp_end` | apply `HΦ` and try to close the goal |
| `wp_pures`, `wp_pure`, `wp_call`, `wp_bind e` | low-level steps |
| `wp_load`, `wp_store`, `wp_alloc l as H`, `wp_alloc_auto` | explicit memory steps |
| `wp_func_call`, `wp_method_call` | unfold `#(functions f ts)` / `#(methods t m v)` |
| `iNamed H`, `iStructNamed H`, `ipersist H`, `iPkgInit` | Perennial-specific proof mode helpers |
| `word`, `len`, `list_elem` | arithmetic and lists |

Details: [`PERENNIAL_PROOF_REFERENCE.md`](PERENNIAL_PROOF_REFERENCE.md).
