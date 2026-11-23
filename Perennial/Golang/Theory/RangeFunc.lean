/-
Iterators (`iter.Seq[E]`, Go 1.23's range functions) and the `for range` rule over them.

* `iter.SeqRuns f R ok`: the function value `f` is an iterator that, run with the resource `R`,
  yields the elements of some list `xs` with `ok xs`, in order, to the yield function it is
  called with, stopping as soon as yield returns `false`, and gives `R` back when it returns. The
  list is chosen when `f` runs (a map's iteration order is), and the caller's yield invariant may
  depend on it.
* `wp_func_for_range1`: `for x := range f { body }` (goose's `func.forRange 1`) over such an `f`:
  the body runs on the elements of `xs` in order, as in `wp_map_for_range`.

Only the single-value form (`iter.Seq`) is covered.
-/
module

public import Perennial.Golang.Theory.Map

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section rangeFunc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]

/-- `f` is an iterator (a Go `iter.Seq[E]` value) over a list with `ok`, needing `R`: called with
`R` and a yield function `yield`, it chooses a list `xs` with `ok xs` and calls `yield` on its
elements in order, each call returning a `bool`; it stops when one returns `false` (calling
`yield` again would be a Go panic) or once all of `xs` is yielded, and then returns `R`. The
caller's yield invariant `I` is chosen once `xs` is known: `I i` holds before the `i`-th call,
and a call returning `false` must leave what the caller needs after `f` returns (`R -∗ Φ #()`).
Not persistent: an iterator that may be run several times is specified by `□ SeqRuns ..`. -/
def iter.SeqRuns {E : Type} (f : GoFunc) (R : IProp GF) (ok : List E → Prop) :
    IProp GF :=
  iprop(∀ (yield : GoFunc) (Φ : val → IProp GF),
    R -∗
    (∀ xs : List E, ⌜ok xs⌝ -∗ ∃ I : Nat → IProp GF,
      I 0 ∗
      □ (∀ (i : Nat) (x : E), ⌜xs[i]? = some x⌝ -∗ I i -∗
          WP (App (Val #yield) (Val #x)) {{ r, ∃ b : Bool, ⌜r = #b⌝ ∗
            (if b then I (i + 1) else (R -∗ Φ #())) }}) ∗
      (I xs.length -∗ R -∗ Φ #())) -∗
    WP (App (Val #f) (Val #yield)) {{ Φ }})

/-- `for x := range f { body }` over an iterator `f` (`iter.SeqRuns f R ok`, with `R`): once `f`
has chosen its list `xs` (`ok xs`), the body runs on `xs[0]`, `xs[1]`, ... from the invariant
`P i`, as in `wp_map_for_range`; a body ending normally or with `continue` goes on with
`P (i + 1)`, and `break`, `return` or a labeled outcome ends the loop with that outcome once `f`
has returned `R` (`forMapPostcondition`; `break` gives `Φ executeVal`). After all of `xs`,
`P xs.length` and `R` give `Φ executeVal`. -/
theorem wp_func_for_range1 {E : Type} (f : GoFunc) (R : IProp GF) (ok : List E → Prop)
    (body : GoFunc) (Φ : val → IProp GF) :
    iter.SeqRuns f R ok -∗ R -∗
    (∀ xs : List E, ⌜ok xs⌝ -∗ ∃ P : Nat → IProp GF,
      P 0 ∗
      □ (∀ (i : Nat) (x : E), ⌜xs[i]? = some x⌝ -∗ P i -∗
          WP (App (Val #body) (Val #x))
            {{ bv, forMapPostcondition (P (i + 1)) (fun v => iprop(R -∗ Φ v)) bv }}) ∗
      (P xs.length -∗ R -∗ Φ executeVal)) -∗
    WP (App (App (Val (func.forRange 1)) (Val #f)) (Val #body)) {{ Φ }} := by
  unfold iter.SeqRuns
  iintro Hf HR HΦ
  rw [func.forRange_unseal]
  unfold func.forRangeDef
  wp_call
  wp_auto
  wp_bind (Alloc (Val executeVal))
  wp_apply_core (wp_alloc_untyped executeVal (by rw [executeVal_unseal]; rfl))
  iintro %exit Hexit
  wp_pures
  wp_bind (App (Val #f) _)
  rw [recv_eq_func_mk]
  iapply Hf $$ HR
  iintro %xs %Hok
  icases HΦ $$ %xs %Hok with ⟨%P, HP, #Hbody, Hfin⟩
  iexists (fun i => iprop(state_ptr ↦ W64 0 ∗ heapPointsto exit (DFrac.own 1) executeVal ∗ P i))
  isplitl [state Hexit HP]
  · dsimp only
    iframe
  isplitr
  · imodintro
    iintro %i %x %Hx ⟨state, Hexit, HP⟩
    have hb : (RecV body.f body.x body.e : val) = #body := by rw [go.intoVal_unfold GoFunc]
    rw [go.intoVal_unfold GoFunc]
    wp_call
    dsimp only at *
    rw [hb]
    wp_auto
    wp_bind (App (Val #body) (Val #x))
    iapply wp_wand $$ (Hbody $$ %i %x %Hx HP)
    iintro %bv Hpost
    unfold forMapPostcondition
    icases Hpost with (⟨%hbv, HP⟩ | ⟨%hbv, HP⟩ | ⟨%hbv, HΦ'⟩ | ⟨%v', %hbv, HΦ'⟩ |
      ⟨%hbv, HΦ'⟩)
    · subst hbv
      rw [continueVal_unseal]; simp only [continueValDef]
      wp_auto
      iexists true
      isplitr
      · ipureintro; rfl
      simp only [↓reduceIte]
      iframe
    · subst hbv
      rw [executeVal_unseal]; simp only [executeValDef]
      wp_auto
      iexists true
      isplitr
      · ipureintro; rfl
      simp only [↓reduceIte]
      iframe
    · subst hbv
      rw [breakVal_unseal]; simp only [breakValDef]
      wp_auto
      wp_bind (App (App (Val Store) (Val #«exit»)) _)
      iapply _internal_wp_untyped_store «exit» _ _ (by simp) $$ Hexit
      inext
      iintro Hexit
      wp_auto
      iexists false
      isplitr
      · ipureintro; rfl
      simp only [Bool.false_eq_true, ↓reduceIte]
      iintro HR
      wp_auto
      wp_bind (App (Val Read) (Val #«exit»))
      iapply _internal_wp_untyped_read «exit» _ _ (by simp) $$ Hexit
      inext
      iintro Hexit
      wp_auto
      rw [executeVal_unseal]
      iapply HΦ' $$ HR
    · subst hbv
      rw [returnVal_unseal]; simp only [returnValDef]
      wp_auto
      wp_bind (App (App (Val Store) (Val #«exit»)) _)
      iapply _internal_wp_untyped_store «exit» _ _ (by simp) $$ Hexit
      inext
      iintro Hexit
      wp_auto
      iexists false
      isplitr
      · ipureintro; rfl
      simp only [Bool.false_eq_true, ↓reduceIte]
      iintro HR
      wp_auto
      wp_bind (App (Val Read) (Val #«exit»))
      iapply _internal_wp_untyped_read «exit» _ _ (by simp) $$ Hexit
      inext
      iintro Hexit
      wp_auto
      iapply HΦ' $$ HR
    · obtain ⟨l, rfl | rfl⟩ := hbv
      · rw [breakToVal_unseal]; simp only [breakToValDef]
        wp_auto
        wp_bind (App (App (Val Store) (Val #«exit»)) _)
        iapply _internal_wp_untyped_store «exit» _ _ (by simp) $$ Hexit
        inext
        iintro Hexit
        wp_auto
        iexists false
        isplitr
        · ipureintro; rfl
        simp only [Bool.false_eq_true, ↓reduceIte]
        iintro HR
        wp_auto
        wp_bind (App (Val Read) (Val #«exit»))
        iapply _internal_wp_untyped_read «exit» _ _ (by simp) $$ Hexit
        inext
        iintro Hexit
        wp_auto
        iapply HΦ' $$ HR
      · rw [continueToVal_unseal]; simp only [continueToValDef]
        wp_auto
        wp_bind (App (App (Val Store) (Val #«exit»)) _)
        iapply _internal_wp_untyped_store «exit» _ _ (by simp) $$ Hexit
        inext
        iintro Hexit
        wp_auto
        iexists false
        isplitr
        · ipureintro; rfl
        simp only [Bool.false_eq_true, ↓reduceIte]
        iintro HR
        wp_auto
        wp_bind (App (Val Read) (Val #«exit»))
        iapply _internal_wp_untyped_read «exit» _ _ (by simp) $$ Hexit
        inext
        iintro Hexit
        wp_auto
        iapply HΦ' $$ HR
  · iintro ⟨state, Hexit, HP⟩ HR
    wp_auto
    wp_bind (App (Val Read) (Val #«exit»))
    iapply _internal_wp_untyped_read «exit» _ executeVal (by rw [executeVal_unseal]; rfl) $$ Hexit
    inext
    iintro Hexit
    rw [executeVal_unseal]; simp only [executeValDef]
    wp_auto
    iapply Hfin $$ HP HR

end rangeFunc

end Perennial
