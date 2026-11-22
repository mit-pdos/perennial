/-
`PureWp` instances for `break:` and
`continue:`, for `break L`/`continue L` (`doBreakTo`, `doContinueTo`, the
outcomes `breakToVal L`/`continueToVal L`, and `catchLabel` at the statement
labeled `L`), the loop rule `wp_for` with its sealed postcondition
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

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

instance pure_continue_val (v1 : val) :
    PureWp (G := G) (L := L) (v1.isPanic = false)
      (App (App (Val exceptionSeq) (Val v1)) (Val continueVal)) (Val continueVal) where
  pure_wp_wp s E Φ K hv := by
    rw [exceptionSeq_unseal, continueVal_unseal]
    simp only [continueValDef]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

instance pure_break_val (v1 : val) :
    PureWp (G := G) (L := L) (v1.isPanic = false)
      (App (App (Val exceptionSeq) (Val v1)) (Val breakVal)) (Val breakVal) where
  pure_wp_wp s E Φ K hv := by
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

section labeled
variable [GooseExts] [GoGlobalContext]

/-- The outcome of `break l`. -/
def breakToValDef (l : GoString) : val := glv((#"breakTo", #l))
@[irreducible] def breakToVal : GoString → val := breakToValDef
theorem breakToVal_unseal : breakToVal = breakToValDef := by with_unfolding_all rfl

/-- The outcome of `continue l`. -/
def continueToValDef (l : GoString) : val := glv((#"continueTo", #l))
@[irreducible] def continueToVal : GoString → val := continueToValDef
theorem continueToVal_unseal : continueToVal = continueToValDef := by
  with_unfolding_all rfl

/-- `bv` is the outcome of `break l` or `continue l` for some label `l`. -/
def isLabeledOutcome (bv : val) : Prop := ∃ l, bv = breakToVal l ∨ bv = continueToVal l

theorem isLabeledOutcome_breakTo (l : GoString) : isLabeledOutcome (breakToVal l) :=
  ⟨l, .inl rfl⟩
theorem isLabeledOutcome_continueTo (l : GoString) : isLabeledOutcome (continueToVal l) :=
  ⟨l, .inr rfl⟩

end labeled

section labeled_wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

instance pure_do_breakTo_val (l : GoString) :
    PureWp (G := G) (L := L) True (App (Val doBreakTo) (Val #l)) (Val (breakToVal l)) where
  pure_wp_wp s E Φ K _ := by
    rw [doBreakTo_unseal, breakToVal_unseal]
    simp only [breakToValDef]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

instance pure_do_continueTo_val (l : GoString) :
    PureWp (G := G) (L := L) True (App (Val doContinueTo) (Val #l)) (Val (continueToVal l)) where
  pure_wp_wp s E Φ K _ := by
    rw [doContinueTo_unseal, continueToVal_unseal]
    simp only [continueToValDef]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

instance pure_breakTo_val (v1 : val) (l : GoString) :
    PureWp (G := G) (L := L) (v1.isPanic = false)
      (App (App (Val exceptionSeq) (Val v1)) (Val (breakToVal l))) (Val (breakToVal l)) where
  pure_wp_wp s E Φ K hv := by
    rw [exceptionSeq_unseal, breakToVal_unseal]
    simp only [breakToValDef]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

instance pure_continueTo_val (v1 : val) (l : GoString) :
    PureWp (G := G) (L := L) (v1.isPanic = false)
      (App (App (Val exceptionSeq) (Val v1)) (Val (continueToVal l))) (Val (continueToVal l)) where
  pure_wp_wp s E Φ K hv := by
    rw [exceptionSeq_unseal, continueToVal_unseal]
    simp only [continueToValDef]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

instance pure_catch_break_breakTo (l : GoString) :
    PureWp (G := G) (L := L) True (App (Val catchBreak) (Val (breakToVal l)))
      (Val (breakToVal l)) :=
  pure_wp_val _ _ _ fun s E Φ _ => by
    rw [catchBreak_unseal, breakToVal_unseal]
    simp only [catchBreakDef, breakToValDef]
    iintro HΦ
    wp_call_lc Hlc
    wp_pures
    iapply HΦ $$ Hlc

instance pure_catch_break_continueTo (l : GoString) :
    PureWp (G := G) (L := L) True (App (Val catchBreak) (Val (continueToVal l)))
      (Val (continueToVal l)) :=
  pure_wp_val _ _ _ fun s E Φ _ => by
    rw [catchBreak_unseal, continueToVal_unseal]
    simp only [catchBreakDef, continueToValDef]
    iintro HΦ
    wp_call_lc Hlc
    wp_pures
    iapply HΦ $$ Hlc

/-! `catchLabel l` (the body of a loop, or a `switch` or `select` statement,
labeled `l`) on each outcome: `break l` and `continue l` become `break` and
`continue`, and the other outcomes (including another label's) are unchanged. -/

instance pure_catch_label_breakTo (l : GoString) :
    PureWp (G := G) (L := L) True (App (App (Val catchLabel) (Val #l)) (Val (breakToVal l)))
      (Val breakVal) :=
  pure_wp_val _ _ _ fun s E Φ _ => by
    rw [catchLabel_unseal, breakToVal_unseal]
    simp only [catchLabelDef, breakToValDef]
    iintro HΦ
    wp_call_lc Hlc
    wp_pures
    rw [decide_eq_true rfl]
    wp_pures
    iapply HΦ $$ Hlc

instance pure_catch_label_continueTo (l : GoString) :
    PureWp (G := G) (L := L) True (App (App (Val catchLabel) (Val #l)) (Val (continueToVal l)))
      (Val continueVal) :=
  pure_wp_val _ _ _ fun s E Φ _ => by
    rw [catchLabel_unseal, continueToVal_unseal]
    simp only [catchLabelDef, continueToValDef]
    iintro HΦ
    wp_call_lc Hlc
    wp_pures
    rw [decide_eq_true rfl]
    wp_pures
    iapply HΦ $$ Hlc

instance (priority := low) pure_catch_label_breakTo_other (l l' : GoString) :
    PureWp (G := G) (L := L) (l' ≠ l)
      (App (App (Val catchLabel) (Val #l)) (Val (breakToVal l'))) (Val (breakToVal l')) :=
  pure_wp_val _ _ _ fun s E Φ h => by
    rw [catchLabel_unseal, breakToVal_unseal]
    simp only [catchLabelDef, breakToValDef]
    iintro HΦ
    wp_call_lc Hlc
    wp_pures
    rw [decide_eq_false h]
    wp_pures
    iapply HΦ $$ Hlc

instance (priority := low) pure_catch_label_continueTo_other (l l' : GoString) :
    PureWp (G := G) (L := L) (l' ≠ l)
      (App (App (Val catchLabel) (Val #l)) (Val (continueToVal l'))) (Val (continueToVal l')) :=
  pure_wp_val _ _ _ fun s E Φ h => by
    rw [catchLabel_unseal, continueToVal_unseal]
    simp only [catchLabelDef, continueToValDef]
    iintro HΦ
    wp_call_lc Hlc
    wp_pures
    rw [decide_eq_false h]
    wp_pures
    iapply HΦ $$ Hlc

instance pure_catch_label_execute (l : GoString) :
    PureWp (G := G) (L := L) True (App (App (Val catchLabel) (Val #l)) (Val executeVal))
      (Val executeVal) :=
  pure_wp_val _ _ _ fun s E Φ _ => by
    rw [catchLabel_unseal, executeVal_unseal]
    simp only [catchLabelDef, executeValDef]
    iintro HΦ
    wp_call_lc Hlc
    wp_pures
    iapply HΦ $$ Hlc

instance pure_catch_label_break (l : GoString) :
    PureWp (G := G) (L := L) True (App (App (Val catchLabel) (Val #l)) (Val breakVal))
      (Val breakVal) :=
  pure_wp_val _ _ _ fun s E Φ _ => by
    rw [catchLabel_unseal, breakVal_unseal]
    simp only [catchLabelDef, breakValDef]
    iintro HΦ
    wp_call_lc Hlc
    wp_pures
    iapply HΦ $$ Hlc

instance pure_catch_label_continue (l : GoString) :
    PureWp (G := G) (L := L) True (App (App (Val catchLabel) (Val #l)) (Val continueVal))
      (Val continueVal) :=
  pure_wp_val _ _ _ fun s E Φ _ => by
    rw [catchLabel_unseal, continueVal_unseal]
    simp only [catchLabelDef, continueValDef]
    iintro HΦ
    wp_call_lc Hlc
    wp_pures
    iapply HΦ $$ Hlc

instance pure_catch_label_return (l : GoString) (v : val) :
    PureWp (G := G) (L := L) True (App (App (Val catchLabel) (Val #l)) (Val (returnVal v)))
      (Val (returnVal v)) :=
  pure_wp_val _ _ _ fun s E Φ _ => by
    rw [catchLabel_unseal, returnVal_unseal]
    simp only [catchLabelDef, returnValDef]
    iintro HΦ
    wp_call_lc Hlc
    wp_pures
    iapply HΦ $$ Hlc

end labeled_wps

noncomputable section for_post
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- The postcondition of a loop body (sealed; use the `wp_for_post_*` lemmas
to prove it). -/
def forPostconditionDef (s : Stuckness) (E : CoPset) (post : val) (P : IProp GF)
    (Φ : val → IProp GF) (bv : val) : IProp GF :=
  iprop((⌜bv = continueVal⌝ ∗ WP (App (Val post) (Val #())) @ s; E {{ v, ⌜v.isPanic = false⌝ ∗ P }}) ∨
    (⌜bv = executeVal⌝ ∗ WP (App (Val post) (Val #())) @ s; E {{ v, ⌜v.isPanic = false⌝ ∗ P }}) ∨
    (⌜bv = breakVal⌝ ∗ Φ executeVal) ∨
    (∃ v, ⌜bv = returnVal v⌝ ∗ Φ bv) ∨
    (∃ p, ⌜bv = PanicV p⌝ ∗ Φ bv) ∨
    (⌜isLabeledOutcome bv⌝ ∗ Φ bv))

@[irreducible] def forPostcondition (s : Stuckness) (E : CoPset) (post : val) (P : IProp GF)
    (Φ : val → IProp GF) (bv : val) : IProp GF :=
  forPostconditionDef s E post P Φ bv

theorem forPostcondition_unseal :
    @forPostcondition = @forPostconditionDef := by
  funext; with_unfolding_all rfl

end for_post

section wp_for
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]
attribute [local instance] pure_test_execute pure_test_continue pure_test_break

/-- The loop rule: given the invariant `P`, a persistent proof that from `P`
the condition evaluates to a boolean, after which (if `true`) the body runs
with postcondition `forPostcondition`. -/
theorem wp_for (P : IProp GF) (s : Stuckness) (E : CoPset) (cond body post : val) (Φ : val → IProp GF)
    (hcond : cond.isPanic = false) (hbody : body.isPanic = false) (hpost : post.isPanic = false) :
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
    icases Hb with (⟨%Hbc, HP⟩ | ⟨%Hbc, HP⟩ | ⟨%Hbc, HΦ⟩ | ⟨%v, %Hbc, HΦ⟩ | ⟨%p, %Hbc, HΦ⟩ |
      ⟨%Hbc, HΦ⟩)
    · subst Hbc
      wp_pures
      wp_apply_core wp_wand $$ HP
      iintro %_ ⟨%_, HP⟩
      ihave HIH := IH $$ HP
      wp_pures
      wp_apply_core wp_wand $$ HIH
      iintro %v HΦ
      cases hv : v.isPanic
      · wp_pures
        iexact HΦ
      · obtain ⟨p, rfl⟩ := val.isPanic_eq_true hv
        wp_pures
        iexact HΦ
    · subst Hbc
      wp_pures
      wp_apply_core wp_wand $$ HP
      iintro %_ ⟨%_, HP⟩
      ihave HIH := IH $$ HP
      wp_pures
      wp_apply_core wp_wand $$ HIH
      iintro %v HΦ
      cases hv : v.isPanic
      · wp_pures
        iexact HΦ
      · obtain ⟨p, rfl⟩ := val.isPanic_eq_true hv
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
    · subst Hbc
      wp_pures
      iexact HΦ
    · obtain ⟨l, rfl | rfl⟩ := Hbc
      · rw [breakToVal_unseal]
        simp only [breakToValDef]
        wp_pures
        iexact HΦ
      · rw [continueToVal_unseal]
        simp only [continueToValDef]
        wp_pures
        iexact HΦ
  · by_cases hc' : c = #false
    · subst hc'
      have : (#false : val) ≠ #true := fun h => absurd (GoGlobalContext.intoVal_inj_bool h) (by decide)
      simp only [_root_.decide_true, ite_true, this, decide_false, Bool.false_eq_true, ite_false]
      wp_pures
      iexact Hbody
    · simp only [hc, hc', decide_false, Bool.false_eq_true, ite_false]
      icases Hbody with %h
      exact h.elim

theorem wp_for_post_do (s : Stuckness) (E : CoPset) (post : val) (P : IProp GF)
    (Φ : val → IProp GF) :
    WP (App (Val post) (Val #())) @ s; E {{ v, ⌜v.isPanic = false⌝ ∗ P }} ⊢
      forPostcondition s E post P Φ executeVal := by
  rw [forPostcondition_unseal]; unfold forPostconditionDef
  iintro H
  iright; ileft
  iframe H
  ipureintro; rfl

theorem wp_for_post_continue (s : Stuckness) (E : CoPset) (post : val) (P : IProp GF)
    (Φ : val → IProp GF) :
    WP (App (Val post) (Val #())) @ s; E {{ v, ⌜v.isPanic = false⌝ ∗ P }} ⊢
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
  iright; iright; iright; ileft
  iexists v
  iframe H
  ipureintro; rfl

/-- A loop body that panics: the loop panics. -/
theorem wp_for_post_panic (s : Stuckness) (E : CoPset) (post : val) (P : IProp GF)
    (Φ : val → IProp GF) (p : val) :
    Φ (PanicV p) ⊢ forPostcondition s E post P Φ (PanicV p) := by
  rw [forPostcondition_unseal]; unfold forPostconditionDef
  iintro H
  iright; iright; iright; iright; ileft
  iexists p
  iframe H
  ipureintro; rfl

/-- A loop body that ends with `break l` or `continue l` for a label `l` other
than the loop's own (caught by `catchLabel` in the body): the loop ends with
that outcome. -/
theorem wp_for_post_labeled (s : Stuckness) (E : CoPset) (post : val) (P : IProp GF)
    (Φ : val → IProp GF) (bv : val) (h : isLabeledOutcome bv) :
    Φ bv ⊢ forPostcondition s E post P Φ bv := by
  rw [forPostcondition_unseal]; unfold forPostconditionDef
  iintro H
  iright; iright; iright; iright; iright
  iframe H
  ipureintro; exact h

end wp_for2

section catch_break
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

/-! `catchBreak` (a `switch` or `select` with a `break` in a case body) on each
outcome of the case body: a `break:` ends the statement normally, and the other
outcomes are unchanged. -/

instance pure_catch_break_break :
    PureWp (G := G) (L := L) True (App (Val catchBreak) (Val breakVal)) (Val executeVal) :=
  pure_wp_val _ _ _ fun s E Φ _ => by
    rw [catchBreak_unseal, breakVal_unseal]
    simp only [catchBreakDef, breakValDef]
    iintro HΦ
    wp_call_lc Hlc
    wp_pures
    iapply HΦ $$ Hlc

instance pure_catch_break_execute :
    PureWp (G := G) (L := L) True (App (Val catchBreak) (Val executeVal)) (Val executeVal) :=
  pure_wp_val _ _ _ fun s E Φ _ => by
    rw [catchBreak_unseal, executeVal_unseal]
    simp only [catchBreakDef, executeValDef]
    iintro HΦ
    wp_call_lc Hlc
    wp_pures
    iapply HΦ $$ Hlc

instance pure_catch_break_continue :
    PureWp (G := G) (L := L) True (App (Val catchBreak) (Val continueVal)) (Val continueVal) :=
  pure_wp_val _ _ _ fun s E Φ _ => by
    rw [catchBreak_unseal, continueVal_unseal]
    simp only [catchBreakDef, continueValDef]
    iintro HΦ
    wp_call_lc Hlc
    wp_pures
    iapply HΦ $$ Hlc

instance pure_catch_break_return (v : val) :
    PureWp (G := G) (L := L) True (App (Val catchBreak) (Val (returnVal v))) (Val (returnVal v)) :=
  pure_wp_val _ _ _ fun s E Φ _ => by
    rw [catchBreak_unseal, returnVal_unseal]
    simp only [catchBreakDef, returnValDef]
    iintro HΦ
    wp_call_lc Hlc
    wp_pures
    iapply HΦ $$ Hlc

end catch_break

set_option hygiene false in
/-- `wp_for_core`: apply `wp_for` to the loop at the head of the goal,
generalizing the whole spatial context into the invariant with `iNamedAccu`,
and introduce the loop-body goal with the invariant destructed by `iNamed`. -/
macro "wp_for_core" : tactic => `(tactic| (
  wp_bind (App (App (App (Val doFor) _) _) _)
  iapply wp_for _ _ _ _ _ _ _ ?hcond ?hbody ?hpost $$ [-] []
  case hcond => rfl
  case hbody => rfl
  case hpost => rfl
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
  | iapply wp_for_post_return
  | iapply wp_for_post_panic
  | (iapply wp_for_post_labeled; first
      | exact isLabeledOutcome_breakTo _
      | exact isLabeledOutcome_continueTo _))

end Perennial
