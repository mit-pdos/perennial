/-
`PureWp` instances for `break:` and
`continue:`, the loop rule `wp_for` with its sealed postcondition
`forPostcondition`, and the tactics `wp_for_core` and `wp_for_post_core`
(the user-facing `wp_for` and `wp_for_post` are in `Auto.lean`).

Loop reasoning:
* use `iassert`/`iNamedAccu` to generalize the current context to the loop
  invariant (`wp_for_core` does this automatically with `iNamedAccu`);
* use `wp_for` with the loop invariant;
* use `wp_for_post` at the loop control points.
-/
module

public import Perennial.Golang.Theory.Exception

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [L : GooseLocalGS GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

instance pure_continue_val (v1 : val) :
    PureWp (G := G) (L := L) True (App (App (Val exceptionSeq) (Val v1)) (Val continueVal))
      (Val continueVal) where
  pure_wp_wp s E Φ K _ := by
    rw [exceptionSeq_unseal, continueVal_unseal]
    simp only [continueValDef]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

instance pure_break_val (v1 : val) :
    PureWp (G := G) (L := L) True (App (App (Val exceptionSeq) (Val v1)) (Val breakVal))
      (Val breakVal) where
  pure_wp_wp s E Φ K _ := by
    rw [exceptionSeq_unseal, breakVal_unseal]
    simp only [breakValDef]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

instance pure_do_continue_val :
    PureWp (G := G) (L := L) True (App (Val doContinue) (Val #())) (Val continueVal) where
  pure_wp_wp s E Φ K _ := by
    rw [doContinue_unseal, continueVal_unseal]
    simp only [continueValDef]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

instance pure_do_break_val :
    PureWp (G := G) (L := L) True (App (Val doBreak) (Val #())) (Val breakVal) where
  pure_wp_wp s E Φ K _ := by
    rw [doBreak_unseal, breakVal_unseal]
    simp only [breakValDef]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

end wps

noncomputable section for_post
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF]

/-- The postcondition of a loop body (sealed; use the `wp_for_post_*` lemmas
to prove it). -/
def forPostconditionDef (s : Stuckness) (E : CoPset) (post : val) (P : IProp GF)
    (Φ : val → IProp GF) (bv : val) : IProp GF :=
  iprop((⌜bv = continueVal⌝ ∗ WP (App (Val post) (Val #())) @ s; E {{ _v, P }}) ∨
    (⌜bv = executeVal⌝ ∗ WP (App (Val post) (Val #())) @ s; E {{ _v, P }}) ∨
    (⌜bv = breakVal⌝ ∗ Φ executeVal) ∨
    (∃ v, ⌜bv = returnVal v⌝ ∗ Φ bv))

@[irreducible] def forPostcondition (s : Stuckness) (E : CoPset) (post : val) (P : IProp GF)
    (Φ : val → IProp GF) (bv : val) : IProp GF :=
  forPostconditionDef s E post P Φ bv

theorem forPostcondition_unseal :
    @forPostcondition = @forPostconditionDef := by
  funext; with_unfolding_all rfl

end for_post

section wp_for
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [L : GooseLocalGS GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

attribute [local instance] go.tagged_internal_inst in
theorem pure_test_execute :
    PureWp (G := G) (L := L) True (Fst (Val executeVal)) (Val #go!"execute") := by
  rw [executeVal_unseal]; simp only [executeValDef]; infer_instance

theorem pure_test_continue :
    PureWp (G := G) (L := L) True (Fst (Val continueVal)) (Val #go!"continue") := by
  rw [continueVal_unseal]; simp only [continueValDef]; infer_instance

theorem pure_test_break :
    PureWp (G := G) (L := L) True (Fst (Val breakVal)) (Val #go!"break") := by
  rw [breakVal_unseal]; simp only [breakValDef]; infer_instance

end wp_for

section wp_for2
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF]
variable [GoSemanticsFunctions] [go.PreSemantics]
attribute [local instance] pure_test_execute pure_test_continue pure_test_break

/-- The loop rule: given the invariant `P`, a persistent proof that from `P`
the condition evaluates to a boolean, after which (if `true`) the body runs
with postcondition `forPostcondition`. -/
theorem wp_for (P : IProp GF) (s : Stuckness) (E : CoPset) (cond body post : val) (Φ : val → IProp GF) :
    P ⊢ □ (P -∗ WP (App (Val cond) (Val #())) @ s; E {{ v,
            if decide (v = #true) then
              WP (App (Val body) (Val #())) @ s; E {{ forPostcondition s E post P Φ }}
            else if decide (v = #false) then Φ executeVal else False }}) -∗
    WP (App (App (App (Val doFor) (Val cond)) (Val body)) (Val post)) @ s; E {{ Φ }} := by
  iintro HP #Hloop
  rw [doFor_unseal, forPostcondition_unseal]
  unfold forPostconditionDef
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
      rw [returnVal_unseal]
      simp only [returnValDef]
      wp_pures
      iexact HΦ
  · by_cases hc' : c = #false
    · subst hc'
      have : (#false : val) ≠ #true := fun h => absurd (GoGlobalContext.intoVal_inj_bool h) (by decide)
      simp only [decide_true, ite_true, this, decide_false, Bool.false_eq_true, ite_false]
      wp_pures
      iexact Hbody
    · simp only [hc, hc', decide_false, Bool.false_eq_true, ite_false]
      icases Hbody with %h
      exact h.elim

theorem wp_for_post_do (s : Stuckness) (E : CoPset) (post : val) (P : IProp GF)
    (Φ : val → IProp GF) :
    WP (App (Val post) (Val #())) @ s; E {{ _v, P }} ⊢
      forPostcondition s E post P Φ executeVal := by
  rw [forPostcondition_unseal]; unfold forPostconditionDef
  iintro H
  iright; ileft
  iframe H
  ipureintro; rfl

theorem wp_for_post_continue (s : Stuckness) (E : CoPset) (post : val) (P : IProp GF)
    (Φ : val → IProp GF) :
    WP (App (Val post) (Val #())) @ s; E {{ _v, P }} ⊢
      forPostcondition s E post P Φ continueVal := by
  rw [forPostcondition_unseal]; unfold forPostconditionDef
  iintro H
  ileft
  iframe H
  ipureintro; rfl

theorem wp_for_post_break (s : Stuckness) (E : CoPset) (post : val) (P : IProp GF)
    (Φ : val → IProp GF) :
    Φ executeVal ⊢ forPostcondition s E post P Φ breakVal := by
  rw [forPostcondition_unseal]; unfold forPostconditionDef
  iintro H
  iright; iright; ileft
  iframe H
  ipureintro; rfl

theorem wp_for_post_return (s : Stuckness) (E : CoPset) (post : val) (P : IProp GF)
    (Φ : val → IProp GF) (v : val) :
    Φ (returnVal v) ⊢ forPostcondition s E post P Φ (returnVal v) := by
  rw [forPostcondition_unseal]; unfold forPostconditionDef
  iintro H
  iright; iright; iright
  iexists v
  iframe H
  ipureintro; rfl

end wp_for2

set_option hygiene false in
/-- `wp_for_core`: apply `wp_for` to the loop at the head of the goal,
generalizing the whole spatial context into the invariant with `iNamedAccu`,
and introduce the loop-body goal with the invariant destructed by `iNamed`. -/
macro "wp_for_core" : tactic => `(tactic| (
  wp_bind (App (App (App (Val doFor) _) _) _)
  iapply wp_for _ _ _ _ _ _ _ $$ [-] []
  iNamedAccu
  iintro !> __CTX
  iNamed __CTX))

/-- `wp_for_post_core`: prove a `forPostcondition` goal with the
appropriate `wp_for_post_*` lemma. -/
macro "wp_for_post_core" : tactic => `(tactic|
  first
  | (iapply wp_for_post_do; wp_pures)
  | iapply wp_for_post_continue
  | iapply wp_for_post_break
  | iapply wp_for_post_return)

end Perennial
