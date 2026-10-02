/-
Companion file for `docs/PERENNIAL_PROOF_TUTORIAL.md`: every Lean code block
in the tutorial is taken from this file. It is not part of the `Perennial`
library; check it with

    lake env lean docs/TutorialExamples.lean

(from the repository root, after `lake build` of the imported modules).

The examples verify functions of goose's unit-test package
`goose/testdata/examples/unittest`, whose generated code lives in
`Perennial/Code/github_com/mit_pdos/perennial/goose/testdata/examples/unittest.lean`.
-/
import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.unittest
import Perennial.Proof.sync_proof.mutex

set_option linter.iris.style.nameCheck false
-- (the library sets this in `lakefile.toml`; `lake env lean` does not read it)
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.unittest

-- ANCHOR: sum_w64
/-- The sum of a list of words (wrapping on overflow, like Go's `+`). -/
def sum_w64 (xs : List w64) : w64 := xs.foldl (· + ·) 0

theorem sum_w64_take_succ (xs : List w64) (n : Nat) (x : w64) (h : xs[n]? = some x) :
    sum_w64 (xs.take (n + 1)) = sum_w64 (xs.take n) + x := by
  unfold sum_w64
  rw [List.take_add_one, List.foldl_append, h]
  rfl

-- ANCHOR_END: sum_w64

-- ANCHOR: context
section tutorial
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics] [package_sem : unittest.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest
-- ANCHOR_END: context

-- ANCHOR: conditionalReturn
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
-- ANCHOR_END: conditionalReturn

-- ANCHOR: conditionalReturn_ifdestruct
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
-- ANCHOR_END: conditionalReturn_ifdestruct

-- ANCHOR: usePtr
/-- `func usePtr() { p := new(uint64); *p = 1; x := *p; *p = x }` -/
theorem wp_usePtr' :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! usePtr)) (Val #()))
    {{ RET #(); True }} := by
  wp_start
  wp_auto
  wp_end
-- ANCHOR_END: usePtr

-- ANCHOR: returnTwo
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
-- ANCHOR_END: returnTwo

-- ANCHOR: writeB
/-- `func (s *S) writeB(two TwoInts) { s.b = two }` -/
theorem wp_S__writeB' (s : loc) (v : S.t) (two : TwoInts.t) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ s ↦ v }}
      (App (Val (s @!! go.type.PointerType S @!! go!"writeB")) (Val #two))
    {{ RET #(); s ↦ ({ v with b' := two } : S.t) }} := by
  wp_start as Hs
  wp_auto
  iapply HΦ $$ Hs
-- ANCHOR_END: writeB

-- ANCHOR: struct
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
-- ANCHOR_END: struct

-- ANCHOR: named
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
-- ANCHOR_END: named

-- ANCHOR: standardForLoop
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
-- ANCHOR_END: standardForLoop

-- ANCHOR: mutex
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
-- ANCHOR_END: mutex

-- ANCHOR: spawn
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
-- ANCHOR_END: spawn

-- ANCHOR: useMap
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
-- ANCHOR_END: useMap

-- ANCHOR: extras
/-- `ifStmtInitialization` stores a function literal `f := func() uint64 {..}`
in a local variable. -/
theorem wp_ifStmtInitialization' (x : w64) :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! ifStmtInitialization)) (Val #x))
    {{ (r : w64), RET #r; True }} := by
  wp_start
  wp_auto      -- with `goose.wp.extras false`, stuck at the store of `f`
  repeat' wp_if_destruct
  all_goals wp_end
-- ANCHOR_END: extras

-- ANCHOR: nosorry
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
-- ANCHOR_END: nosorry

end tutorial


/-! ## Ghost state and invariants -/

section ghost
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF] [allG GF]

-- ANCHOR: ghost
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
-- ANCHOR_END: ghost

end ghost

end github_com.mit_pdos.perennial.goose.testdata.examples.unittest

/-! ## Arithmetic -/

-- ANCHOR: word
example (x : w64) (h : uint.Z x < 10) : uint.Z (x + W64 1) = uint.Z x + 1 := by word
example (x y : w64) (h : sint.Z x ≤ sint.Z y) (h' : 0 ≤ sint.Z x) : 0 ≤ sint.Z y := by word
example (l : List Nat) (n : Nat) (h : n ≤ l.length) : (l.take n ++ [3]).length = n + 1 := by len
example (l : List w64) (h : 2 < l.length) : True := by
  list_elem l 2 as y          -- `y : w64` and `Hy_lookup : l[2]? = some y`
  trivial
-- ANCHOR_END: word

/-! ## Iris proof mode examples (for `docs/IRIS_PROOF_MODE.md`) -/

section ipm
-- Iris's `IProp` is affine: hypotheses may be dropped
variable {PROP : Type _} [BI PROP] [BIAffine PROP]

-- ANCHOR: ipm_intro
example (P Q : PROP) (Φ : Nat → PROP) :
    ⊢ P ∗ Q -∗ (∀ n, Φ n) -∗ Q ∗ Φ 3 ∗ P := by
  iintro ⟨HP, HQ⟩ HΦ
  isplitl [HQ]
  · iexact HQ
  isplitl [HΦ]
  · iapply HΦ
  · iexact HP
-- ANCHOR_END: ipm_intro

-- ANCHOR: ipm_cases
example (P Q R : PROP) (φ : Prop) (Ψ : Nat → PROP) :
    ⊢ (∃ n, Ψ n ∗ ⌜φ⌝) -∗ □ R -∗ (P ∨ Q) -∗ (∃ n, Ψ n) ∗ R ∗ (Q ∨ P) := by
  iintro ⟨%n, HΨ, %Hφ⟩ #HR (HP | HQ)
  · iframe HΨ HR     -- `iframe` also instantiates the `∃ n`
    iright
    iexact HP
  · iframe HΨ HR
    ileft
    iexact HQ
-- ANCHOR_END: ipm_cases

-- ANCHOR: ipm_spec
example (P Q R : PROP) :
    ⊢ (P -∗ Q -∗ R) -∗ P -∗ Q -∗ R := by
  iintro H HP HQ
  -- give `HP` to the first premise, frame `HQ` into the second
  iapply H $$ HP [$HQ]

example (P Q R : PROP) :
    ⊢ (P -∗ Q) -∗ (Q -∗ R) -∗ P -∗ R := by
  iintro HPQ HQR HP
  ihave HQ := HPQ $$ HP
  ispecialize HQR $$ HQ
  iexact HQR

example (P : PROP) (Φ : Nat → PROP) :
    ⊢ (∀ n, P -∗ Φ n) -∗ P -∗ Φ 7 := by
  iintro H HP
  -- `%t` instantiates a universal quantifier
  iapply H $$ %7 HP
-- ANCHOR_END: ipm_spec

-- ANCHOR: ipm_have
example (P Q : PROP) [Persistent Q] (h : P ⊢ Q) :
    ⊢ P -∗ Q ∗ P := by
  iintro HP
  -- `ihave pat : prop $$ spat` (Rocq `iAssert`): the new goal `Q` gets `HP`;
  -- since `Q` is persistent (`#HQ`), `HP` also stays available afterwards
  ihave #HQ : Q $$ [HP]
  · iapply h; iexact HP
  iframe # ∗
-- ANCHOR_END: ipm_have

-- ANCHOR: ipm_pure
example (P : PROP) (x y : Nat) (h : x = y) :
    ⊢ P -∗ P ∗ ⌜y = x⌝ := by
  iintro HP
  iframe
  ipureintro
  exact h.symm

example (P : PROP) (φ : Prop) :
    ⊢ ⌜φ⌝ ∗ P -∗ P := by
  iintro ⟨Hφ, HP⟩
  ipure Hφ          -- move the pure hypothesis to the Lean context
  iexact HP
-- ANCHOR_END: ipm_pure

-- ANCHOR: ipm_exists
example (Φ : Nat → PROP) :
    ⊢ Φ 1 -∗ ∃ n, Φ n := by
  iintro H
  iexists 1
  iexact H

example (Φ : Nat → Nat → PROP) :
    ⊢ Φ 1 2 -∗ ∃ n m, Φ n m := by
  iintro H
  iexists _, _
  iexact H
-- ANCHOR_END: ipm_exists

-- ANCHOR: ipm_frame
example (P Q R : PROP) :
    ⊢ □ R -∗ P -∗ Q -∗ R ∗ Q ∗ P := by
  iintro #HR HP HQ
  iframe HP
  iframe # ∗
-- ANCHOR_END: ipm_frame

-- ANCHOR: ipm_misc
example (P Q : PROP) :
    ⊢ P -∗ Q -∗ P := by
  iintro HP HQ
  iclear HQ
  irename HP => H
  iexact H
-- ANCHOR_END: ipm_misc

end ipm

section ipm_loeb
variable {PROP : Type _} [BI PROP] [BILoeb PROP]

-- ANCHOR: ipm_loeb
example (P : PROP) : ⊢ ▷ P -∗ ▷ P := by
  iintro HP
  iloeb as IH
  iexact HP
-- ANCHOR_END: ipm_loeb

end ipm_loeb

section ipm_mod
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]

-- ANCHOR: ipm_mod
example (P Q : IProp GF) (E : CoPset) :
    ⊢ (|==> P) -∗ ▷ Q -∗ |={E}=> P ∗ ▷ Q := by
  iintro HP HQ
  imod HP            -- eliminate the update, keeping the name `HP`
  imodintro          -- introduce `|={E}=>`
  iframe

example (P : IProp GF) [Timeless P] (E : CoPset) :
    ⊢ ▷ P -∗ |={E}=> P := by
  iintro >HP         -- strip the later of a timeless proposition
  imodintro
  iexact HP

example (P Q : IProp GF) :
    ⊢ ▷ P -∗ ▷ Q -∗ ▷ (P ∗ Q) := by
  iintro HP HQ
  inext              -- strips `▷` from the goal and the hypotheses
  iframe
-- ANCHOR_END: ipm_mod

-- ANCHOR: precedence
-- `|==>` (and `▷`, `□`) bind tighter than `∗`; `|={E}=>` extends to the right.
example (P Q : IProp GF) : iprop(|==> P ∗ Q) = iprop((|==> P) ∗ Q) := rfl
example (P Q : IProp GF) (E : CoPset) : iprop(|={E}=> P ∗ Q) = iprop(|={E}=> (P ∗ Q)) := rfl
example (P Q : IProp GF) : iprop(▷ P ∗ Q) = iprop((▷ P) ∗ Q) := rfl
-- ANCHOR_END: precedence

end ipm_mod

/-! ## Package initialization (the shape of `Perennial/Proof/sync_proof/base.lean`) -/

namespace sync

section pkg_init
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

-- ANCHOR: pkg_init
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
-- ANCHOR_END: pkg_init

end pkg_init

end sync

end Perennial
