/-
The proof of `errors.is`.
-/
module

public import Perennial.Spec.errors.is_

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : errors.Assumptions]

/-- By Löb induction (for the recursive calls on the errors of an `Unwrap() []error`). -/
theorem errors.is.wp_proof :
    errors.is.spec (GF := GF) (hG := hG) := by
  intro S M err target c hS hc
  iloeb as IH generalizing %err %hS
  irevert IH
  iapply asTypeHide_intro
  iintro #IH
  wp_start as #Htree
  wp_auto
  ihave HI : (∃ e : GoError,
      "err" ∷ err_ptr ↦ e ∗ "%HSe" ∷ ⌜S e⌝ ∗
      "%He" ∷ ⌜(c = true ∧ err ≠ interface.nil ∧ err = target) → e = err⌝ : IProp GF) $$ [err]
  · iexists err
    iframe
    ipureintro; exact ⟨hS, fun _ => rfl⟩
  wp_for HI
  -- the comparison `targetComparable && err == target`, joined
  wp_bind (If _ _ _)
  iapply wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ⌜c = true → e ≠ target⌝ ∗
      "target" ∷ target_ptr ↦ target ∗ "err" ∷ err_ptr ↦ e ∗ "targetComparable" ∷ targetComparable_ptr ↦ c ∨
      ⌜v = returnVal #true ∧ c = true ∧ e = target⌝)) $$ [target err targetComparable]
  · cases c
    · wp_auto
      ileft
      iframe
      ipureintro; simp
    obtain ⟨⟨tii, rfl, T, l, hT, hl⟩, htyped⟩ := hc rfl
    wp_auto
    cases e with
    | nil =>
      dsimp only
      wp_auto
      ileft
      iframe
      ipureintro; exact ⟨rfl, fun _ h => by cases h⟩
    | ok ii =>
      dsimp only
      by_cases hty : ii.ty = tii.ty
      · obtain ⟨l', hl'⟩ := htyped ii tii HSe rfl hty
        simp only [hty, ↓reduceIte, hT, hl, hl']
        wp_auto
        have hii : ∀ jj : GoInterfaceOk, jj.ty = tii.ty → jj.v = tii.v → jj = tii := by
          intro jj h1 h2; cases jj; cases tii; simp_all
        wp_if_destruct
        · subst Hif
          iright
          ipureintro
          refine ⟨trivial, trivial, ?_⟩
          rw [hii ii hty (by rw [hl', hl])]
        · ileft
          iframe
          ipureintro
          intro _ h
          apply Hif
          cases h
          rw [hl] at hl'
          exact (go.intoVal_inj hl').symm
      · simp only [hty, ↓reduceIte]
        wp_auto
        ileft
        iframe
        ipureintro
        refine ⟨rfl, fun _ h => hty ?_⟩
        cases h; rfl
  iintro %v Hv
  icases Hv with (⟨%Hv, %Hne, target, err, targetComparable⟩ | %Hret)
  rotate_left
  · obtain ⟨rfl, rfl, rfl⟩ := Hret
    wp_auto
    wp_for_post
    iapply HΦ
    ipureintro
    obtain ⟨⟨tii, rfl, -⟩, -⟩ := hc rfl
    exact ⟨fun _ => ⟨tii, HSe, Or.inl rfl⟩, fun h => by cases h⟩
  subst Hv
  wp_auto
  -- the final `b = false` obligation, at every `return false`
  have Hfalse : c = true → err ≠ interface.nil → err ≠ target := by
    intro hc1 hn heq
    exact Hne hc1 ((He ⟨hc1, hn, heq⟩).trans heq)
  cases e with
  | nil =>
    dsimp only
    wp_auto
    wp_for_post
    iapply HΦ
    ipureintro
    exact ⟨fun h => absurd h (by decide), fun _ => Hfalse⟩
  | ok ii =>
    ihave Hnode := Htree $$ %ii %HSe
    iNamed Hnode
    dsimp only
    have huIs : underlying (go.InterfaceType [go.MethodElem go!"Is" (go.Signature [go.error] false [go.bool])]) =
        go.InterfaceType [go.MethodElem go!"Is" (go.Signature [go.error] false [go.bool])] :=
      go.is_underlying
    -- the `Is` method, joined before the `Unwrap` switch
    wp_join (Q := fun v => iprop(
        (⌜v = executeVal⌝ ∗ "err" ∷ err_ptr ↦ (interface.ok ii : GoError) ∗
          "target" ∷ target_ptr ↦ target ∗ "targetComparable" ∷ targetComparable_ptr ↦ c) ∨
        ⌜v = returnVal #true ∧ M ii⌝)) at next 2 with [err target targetComparable x ok]
    cases hIs : go.typeSetContains ii.ty
      (go.InterfaceType [go.MethodElem go!"Is" (go.Signature [go.error] false [go.bool])])
    case' true =>
      simp only [go.typeSetContains, huIs, go.typeSetElemsContains, go.typeSetElemContains,
        List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq] at hIs
      simp only [hIs, ↓reduceIte]
      wp_auto
      wp_apply HIs as %b %Hb
      cases b
      case true =>
        wp_auto
        iright; ipureintro; exact ⟨rfl, Hb rfl⟩
      wp_auto
      ileft; iframe; ipureintro; rfl
    case' false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      ileft; iframe; ipureintro; rfl
    iintro HQ
    icases HQ with (⟨%Hv, err, target, targetComparable⟩ | %Hret)
    rotate_left
    · obtain ⟨rfl, hM⟩ := Hret
      wp_auto
      wp_for_post
      iapply HΦ
      ipureintro
      exact ⟨fun _ => ⟨ii, HSe, Or.inr hM⟩, fun h => absurd h (by decide)⟩
    subst Hv
    wp_auto
    have hu1 : underlying (go.InterfaceType
        [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])]) =
        go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])] :=
      go.is_underlying
    have hu2 : underlying (go.InterfaceType
        [go.MethodElem go!"Unwrap" (go.Signature [] false [go.GoType.SliceType go.error])]) =
        go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.GoType.SliceType go.error])] :=
      go.is_underlying
    -- a new error of the tree, to continue the loop with
    have Hnext : ∀ e' : GoError, (c = true ∧ err ≠ interface.nil ∧ err = target) → e' = err := by
      intro e' h
      exact absurd ((He h).trans h.2.2) (Hne h.1)
    cases hU : go.typeSetContains ii.ty
      (go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])])
    case true =>
      simp only [go.typeSetContains, hu1, go.typeSetElemsContains, go.typeSetElemContains,
        List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq] at hU
      simp only [hU, ↓reduceIte]
      wp_auto
      wp_apply HUnwrap as %e' %HSe'
      cases e' with
      | nil =>
        wp_auto
        wp_for_post
        iapply HΦ
        ipureintro
        exact ⟨fun h => absurd h (by decide), fun _ => Hfalse⟩
      | ok ii' =>
        wp_auto
        wp_for_post
        iframe
        iexists _
        iframe
        ipureintro
        exact ⟨HSe', Hnext _⟩
    case false =>
      simp only [go.typeSetContains, hu1, go.typeSetElemsContains, go.typeSetElemContains,
        List.all_cons, List.all_nil, Bool.and_true, decide_eq_false_iff_not] at hU
      simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      cases hU2 : go.typeSetContains ii.ty
        (go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.GoType.SliceType go.error])])
      case true =>
        simp only [go.typeSetContains, hu2, go.typeSetElemsContains, go.typeSetElemContains,
          List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq] at hU2
        simp only [hU, ↓reduceIte]
        simp only [hU2, ↓reduceIte]
        wp_auto
        wp_apply HUnwrap as %s %dq %es ⟨Hs, %Hes⟩
        ihave %Hlen := ownSlice_len _ _ _ $$ Hs
        ihave HI2 : (∃ (j : w64) (e2 : GoError),
            "i" ∷ i_ptr ↦ j ∗ "Hs" ∷ s ↦*{dq} es ∗ "err" ∷ err_ptr ↦ e2 ∗
            "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len⌝ : IProp GF) $$ [i Hs err]
        · iexists W64 0, _
          iframe
          ipureintro; word
        wp_for HI2
        wp_if_destruct
        · simp only [Hj.1, Hif, _root_.and_self, ↓reduceIte]
          list_elem es (sint.nat j) as e2'
          irevert IH
          iapply asTypeHide_elim
          iintro #IH
          wp_apply wp_load_slice_index s (sint.Z j) es dq e2' Hj.1 $$ [Hs] with Hs
          · iframe; ipureintro; exact He2'_lookup
          have HSe2' : S e2' := Hes e2' (List.mem_of_getElem? He2'_lookup)
          (try wp_auto)
          wp_apply IH $$ %e2' %HSe2' [] as %b0 ⟨%Hb0, -⟩
          · iframe #
          cases b0
          case true =>
            wp_auto
            wp_for_post
            wp_for_post
            iapply HΦ
            ipureintro
            exact ⟨fun _ => Hb0 rfl, fun h => absurd h (by decide)⟩
          case false =>
            wp_auto
            wp_for_post
            iframe
            iexists j + W64 1, _
            iframe
            ipureintro; word
        · wp_for_post
          iapply HΦ
          ipureintro
          exact ⟨fun h => absurd h (by decide), fun _ => Hfalse⟩
      case false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        wp_auto
        wp_for_post
        iapply HΦ
        ipureintro
        exact ⟨fun h => absurd h (by decide), fun _ => Hfalse⟩

end proof

end Perennial
