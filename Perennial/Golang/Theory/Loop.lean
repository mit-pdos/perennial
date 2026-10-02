/-
Port of `new/golang/theory/loop.v`: `PureWp` instances for `break:` and
`continue:`, the loop rule `wp_for` with its sealed postcondition
`for_postcondition`, and the tactics `wp_for_core` and `wp_for_post_core`
(the user-facing `wp_for` and `wp_for_post` are in `Auto.lean`).

Loop reasoning:
* use `iassert`/`iNamedAccu` to generalize the current context to the loop
  invariant (`wp_for_core` does this automatically with `iNamedAccu`);
* use `wp_for` with the loop invariant;
* use `wp_for_post` at the loop control points.
-/
import Perennial.Golang.Theory.Exception

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : gooseGlobalGS hlc GF] [L : gooseLocalGS GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

instance pure_continue_val (v1 : val) :
    PureWp (G := G) (L := L) True (App (App (Val exception_seq) (Val v1)) (Val continue_val))
      (Val continue_val) where
  pure_wp_wp s E Φ K _ := by
    rw [exception_seq_unseal, continue_val_unseal]
    simp only [continue_val_def]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

instance pure_break_val (v1 : val) :
    PureWp (G := G) (L := L) True (App (App (Val exception_seq) (Val v1)) (Val break_val))
      (Val break_val) where
  pure_wp_wp s E Φ K _ := by
    rw [exception_seq_unseal, break_val_unseal]
    simp only [break_val_def]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

instance pure_do_continue_val :
    PureWp (G := G) (L := L) True (App (Val do_continue) (Val #())) (Val continue_val) where
  pure_wp_wp s E Φ K _ := by
    rw [do_continue_unseal, continue_val_unseal]
    simp only [continue_val_def]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

instance pure_do_break_val :
    PureWp (G := G) (L := L) True (App (Val do_break) (Val #())) (Val break_val) where
  pure_wp_wp s E Φ K _ := by
    rw [do_break_unseal, break_val_unseal]
    simp only [break_val_def]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

end wps

noncomputable section for_post
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]

/-- The postcondition of a loop body (sealed; use the `wp_for_post_*` lemmas
to prove it). -/
def for_postcondition_def (s : Stuckness) (E : CoPset) (post : val) (P : IProp GF)
    (Φ : val → IProp GF) (bv : val) : IProp GF :=
  iprop((⌜bv = continue_val⌝ ∗ WP (App (Val post) (Val #())) @ s; E {{ _v, P }}) ∨
    (⌜bv = execute_val⌝ ∗ WP (App (Val post) (Val #())) @ s; E {{ _v, P }}) ∨
    (⌜bv = break_val⌝ ∗ Φ execute_val) ∨
    (∃ v, ⌜bv = return_val v⌝ ∗ Φ bv))

@[irreducible] def for_postcondition (s : Stuckness) (E : CoPset) (post : val) (P : IProp GF)
    (Φ : val → IProp GF) (bv : val) : IProp GF :=
  for_postcondition_def s E post P Φ bv

theorem for_postcondition_unseal :
    @for_postcondition = @for_postcondition_def := by
  funext; with_unfolding_all rfl

end for_post

section wp_for
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : gooseGlobalGS hlc GF] [L : gooseLocalGS GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

attribute [local instance] go.tagged_internal_inst in
theorem pure_test_execute :
    PureWp (G := G) (L := L) True (Fst (Val execute_val)) (Val #go!"execute") := by
  rw [execute_val_unseal]; simp only [execute_val_def]; infer_instance

theorem pure_test_continue :
    PureWp (G := G) (L := L) True (Fst (Val continue_val)) (Val #go!"continue") := by
  rw [continue_val_unseal]; simp only [continue_val_def]; infer_instance

theorem pure_test_break :
    PureWp (G := G) (L := L) True (Fst (Val break_val)) (Val #go!"break") := by
  rw [break_val_unseal]; simp only [break_val_def]; infer_instance

end wp_for

section wp_for2
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]
attribute [local instance] pure_test_execute pure_test_continue pure_test_break

/-- The loop rule: given the invariant `P`, a persistent proof that from `P`
the condition evaluates to a boolean, after which (if `true`) the body runs
with postcondition `for_postcondition`. -/
theorem wp_for (P : IProp GF) (s : Stuckness) (E : CoPset) (cond body post : val) (Φ : val → IProp GF) :
    P ⊢ □ (P -∗ WP (App (Val cond) (Val #())) @ s; E {{ v,
            if decide (v = #true) then
              WP (App (Val body) (Val #())) @ s; E {{ for_postcondition s E post P Φ }}
            else if decide (v = #false) then Φ execute_val else False }}) -∗
    WP (App (App (App (Val do_for) (Val cond)) (Val body)) (Val post)) @ s; E {{ Φ }} := by
  iintro HP #Hloop
  rw [do_for_unseal, for_postcondition_unseal]
  unfold for_postcondition_def
  iloeb as IH generalizing HP
  wp_call
  ihave Hloop1 := Hloop $$ HP
  wp_apply_core wp_wand $$ Hloop1
  iintro %c Hbody
  by_cases hc : c = #true
  · subst hc
    simp only [decide_true, ite_true]
    wp_pures
    wp_apply_core wp_wand $$ Hbody
    iintro %bc Hb
    icases Hb with (⟨%Hbc, HP⟩ | ⟨%Hbc, HP⟩ | ⟨%Hbc, HΦ⟩ | ⟨%v, %Hbc, HΦ⟩)
    · subst Hbc
      wp_pures
      wp_apply_core wp_wand $$ HP
      iintro %_ HP
      ihave HIH := IH $$ HP
      wp_pures
      wp_apply_core wp_wand $$ HIH
      iintro %v HΦ
      wp_pures
      iexact HΦ
    · subst Hbc
      wp_pures
      wp_apply_core wp_wand $$ HP
      iintro %_ HP
      ihave HIH := IH $$ HP
      wp_pures
      wp_apply_core wp_wand $$ HIH
      iintro %v HΦ
      wp_pures
      iexact HΦ
    · subst Hbc
      wp_pures
      iexact HΦ
    · subst Hbc
      rw [return_val_unseal]
      simp only [return_val_def]
      wp_pures
      iexact HΦ
  · by_cases hc' : c = #false
    · subst hc'
      have : (#false : val) ≠ #true := fun h => absurd (GoGlobalContext.into_val_inj_bool h) (by decide)
      simp only [decide_true, ite_true, this, decide_false, Bool.false_eq_true, ite_false]
      wp_pures
      iexact Hbody
    · simp only [hc, hc', decide_false, Bool.false_eq_true, ite_false]
      icases Hbody with %h
      exact h.elim

theorem wp_for_post_do (s : Stuckness) (E : CoPset) (post : val) (P : IProp GF)
    (Φ : val → IProp GF) :
    WP (App (Val post) (Val #())) @ s; E {{ _v, P }} ⊢
      for_postcondition s E post P Φ execute_val := by
  rw [for_postcondition_unseal]; unfold for_postcondition_def
  iintro H
  iright; ileft
  iframe H
  ipureintro; rfl

theorem wp_for_post_continue (s : Stuckness) (E : CoPset) (post : val) (P : IProp GF)
    (Φ : val → IProp GF) :
    WP (App (Val post) (Val #())) @ s; E {{ _v, P }} ⊢
      for_postcondition s E post P Φ continue_val := by
  rw [for_postcondition_unseal]; unfold for_postcondition_def
  iintro H
  ileft
  iframe H
  ipureintro; rfl

theorem wp_for_post_break (s : Stuckness) (E : CoPset) (post : val) (P : IProp GF)
    (Φ : val → IProp GF) :
    Φ execute_val ⊢ for_postcondition s E post P Φ break_val := by
  rw [for_postcondition_unseal]; unfold for_postcondition_def
  iintro H
  iright; iright; ileft
  iframe H
  ipureintro; rfl

theorem wp_for_post_return (s : Stuckness) (E : CoPset) (post : val) (P : IProp GF)
    (Φ : val → IProp GF) (v : val) :
    Φ (return_val v) ⊢ for_postcondition s E post P Φ (return_val v) := by
  rw [for_postcondition_unseal]; unfold for_postcondition_def
  iintro H
  iright; iright; iright
  iexists v
  iframe H
  ipureintro; rfl

end wp_for2

set_option hygiene false in
/-- Rocq `wp_for_core`: apply `wp_for` to the loop at the head of the goal,
generalizing the whole spatial context into the invariant with `iNamedAccu`,
and introduce the loop-body goal with the invariant destructed by `iNamed`. -/
macro "wp_for_core" : tactic => `(tactic| (
  wp_bind (App (App (App (Val do_for) _) _) _)
  iapply wp_for _ _ _ _ _ _ _ $$ [-] []
  iNamedAccu
  iintro !> __CTX
  iNamed __CTX))

/-- Rocq `wp_for_post_core`: prove a `for_postcondition` goal with the
appropriate `wp_for_post_*` lemma. -/
macro "wp_for_post_core" : tactic => `(tactic|
  first
  | (iapply wp_for_post_do; wp_pures)
  | iapply wp_for_post_continue
  | iapply wp_for_post_break
  | iapply wp_for_post_return)

end Perennial
