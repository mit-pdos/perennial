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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : errors.Assumptions]

/-- By Löb induction (for the recursive calls on the errors of an `Unwrap() []error`). -/
theorem errors.is.wp_proof :
    errors.is.spec (GF := GF) (hG := hG) := by
  intro S I U err target c hS hc
  iloeb as IH generalizing %err %hS
  irevert IH
  iapply asTypeHide_intro
  iintro #IH
  wp_start as #Htree
  wp_auto
  ihave HI : (∃ e : GoError,
      "err" ∷ err_ptr ↦ e ∗ "%HSe" ∷ ⌜S e⌝ ∗
      "%He" ∷ ⌜∀ b, IsWalk c I U target e b → IsWalk c I U target err b⌝ : IProp GF) $$ [err]
  · iexists err
    iframe
    ipureintro; exact ⟨hS, fun _ h => h⟩
  wp_for HI
  -- the comparison `targetComparable && err == target`, joined
  wp_bind (If _ _ _)
  iapply wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ⌜c = true → e ≠ target⌝ ∗
      "target" ∷ target_ptr ↦ target ∗ "err" ∷ err_ptr ↦ e ∗ "targetComparable" ∷ targetComparable_ptr ↦ c ∗
      "«$res0»" ∷ «$res0_ptr» ↦ zero_val Bool ∨
      ⌜v = returnVal #() ∧ c = true ∧ e = target⌝ ∗ «$res0_ptr» ↦ true)) $$ [target err targetComparable «$res0»]
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
          iframe
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
  icases Hv with (⟨%Hv, %Hne, target, err, targetComparable, «$res0»⟩ | ⟨%Hret, «$res0»⟩)
  rotate_left
  · obtain ⟨rfl, rfl, rfl⟩ := Hret
    wp_auto
    wp_for_post
    iapply HΦ
    ipureintro
    obtain ⟨⟨tii, rfl, -⟩, -⟩ := hc rfl
    exact He _ (.eq rfl rfl)
  subst Hv
  wp_auto
  have Htnil : c = true → target ≠ interface.nil := by
    intro hc1 h
    obtain ⟨⟨tii, ht, -⟩, -⟩ := hc hc1
    rw [ht] at h; cases h
  cases e with
  | nil =>
    dsimp only
    wp_auto
    wp_for_post
    iapply HΦ
    ipureintro
    exact He _ (.nilSkip Htnil .done)
  | ok ii =>
    ihave Hnode := Htree $$ %ii %HSe
    iNamed Hnode
    dsimp only
    have huIs : underlying (go.InterfaceType [go.MethodElem go!"Is" (go.Signature [go.error] false [go.bool])]) =
        go.InterfaceType [go.MethodElem go!"Is" (go.Signature [go.error] false [go.bool])] :=
      go.is_underlying
    -- the `Is` method, joined before the `Unwrap` switch
    wp_join (Q := fun v => iprop(
        (⌜v = executeVal ∧ I ii false⌝ ∗ "err" ∷ err_ptr ↦ (interface.ok ii : GoError) ∗
          "target" ∷ target_ptr ↦ target ∗ "targetComparable" ∷ targetComparable_ptr ↦ c ∗
          "«$res0»" ∷ «$res0_ptr» ↦ zero_val Bool) ∨
        ⌜v = returnVal #() ∧ I ii true⌝ ∗ «$res0_ptr» ↦ true)) at next
      with [err target targetComparable «$res0»]
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
        iright; iframe; ipureintro; exact ⟨rfl, Hb⟩
      wp_auto
      ileft; iframe; ipureintro; exact ⟨rfl, Hb⟩
    case' false =>
      simp only [go.typeSetContains, huIs, go.typeSetElemsContains, go.typeSetElemContains,
        List.all_cons, List.all_nil, Bool.and_true, decide_eq_false_iff_not] at hIs
      simp only [hIs, Bool.false_eq_true, ↓reduceIte]
      icases HIs with %hI
      wp_auto
      ileft; iframe; ipureintro; exact ⟨rfl, hI⟩
    iintro HQ
    icases HQ with (⟨%Hv, err, target, targetComparable, «$res0»⟩ | ⟨%Hret, «$res0»⟩)
    rotate_left
    · obtain ⟨rfl, hI⟩ := Hret
      wp_auto
      wp_for_post
      iapply HΦ
      ipureintro
      exact He _ (.is Hne hI)
    obtain ⟨rfl, hIf⟩ := Hv
    wp_auto
    have hu1 : underlying (go.InterfaceType
        [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])]) =
        go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])] :=
      go.is_underlying
    have hu2 : underlying (go.InterfaceType
        [go.MethodElem go!"Unwrap" (go.Signature [] false [go.GoType.SliceType go.error])]) =
        go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.GoType.SliceType go.error])] :=
      go.is_underlying
    cases hU : go.typeSetContains ii.ty
      (go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])])
    case true =>
      simp only [go.typeSetContains, hu1, go.typeSetElemsContains, go.typeSetElemContains,
        List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq] at hU
      simp only [hU, ↓reduceIte]
      wp_auto
      wp_apply HUnwrap as %e' ⟨%HSe', %hU1⟩
      cases e' with
      | nil =>
        wp_auto
        wp_for_post
        iapply HΦ
        ipureintro
        exact He _ (IsWalk.children Hne hIf hU1 (.nilSkip Htnil .done))
      | ok ii' =>
        wp_auto
        wp_for_post
        iframe
        iexists _
        iframe
        ipureintro
        exact ⟨HSe', fun b h => He b (IsWalk.children Hne hIf hU1 h)⟩
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
        wp_apply HUnwrap as %s %dq %es ⟨Hs, %Hes, %hUs⟩
        ihave %Hlen := ownSlice_len _ _ _ $$ Hs
        ihave HI2 : (∃ (j : w64) (e2 : GoError),
            "i" ∷ i_ptr ↦ j ∗ "Hs" ∷ s ↦*{dq} es ∗ "err" ∷ err_ptr ↦ e2 ∗
            "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len⌝ ∗
            "%Hd" ∷ ⌜∀ b, IsWalkL c I U target (es.drop (sint.nat j)) b →
              IsWalkL c I U target es b⌝ : IProp GF) $$ [i Hs err]
        · iexists W64 0, _
          iframe
          ipureintro; exact ⟨by word, fun _ h => h⟩
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
          wp_apply IH $$ %e2' %HSe2' [] as %b0 %Hb0
          · iframe #
          have hlt : sint.nat j < es.length := (List.getElem?_eq_some_iff.mp He2'_lookup).1
          have hdrop : es.drop (sint.nat j) = e2' :: es.drop (sint.nat (j + W64 1)) := by
            rw [List.drop_eq_getElem_cons hlt,
              (List.getElem?_eq_some_iff.mp He2'_lookup).2,
              show sint.nat (j + W64 1) = sint.nat j + 1 by word]
          cases b0
          case true =>
            wp_auto
            wp_for_post
            wp_for_post
            iapply HΦ
            ipureintro
            exact He _ (IsWalk.children Hne hIf hUs (Hd _ (hdrop ▸ IsWalkL.cons_true Hb0)))
          case false =>
            wp_auto
            wp_for_post
            iframe
            iexists j + W64 1, _
            iframe
            ipureintro
            exact ⟨by word, fun b h => Hd b (hdrop ▸ IsWalkL.cons_false Hb0 h)⟩
        · wp_for_post
          iapply HΦ
          ipureintro
          have hnil : es.drop (sint.nat j) = [] := List.drop_eq_nil_of_le (by word)
          exact He _ (IsWalk.children Hne hIf hUs (Hd _ (hnil ▸ .done)))
      case false =>
        simp only [go.typeSetContains, hu2, go.typeSetElemsContains, go.typeSetElemContains,
          List.all_cons, List.all_nil, Bool.and_true, decide_eq_false_iff_not] at hU2
        simp only [hU, hU2, Bool.false_eq_true, ↓reduceIte]
        icases HUnwrap with %hU0
        wp_auto
        wp_for_post
        iapply HΦ
        ipureintro
        exact He _ (IsWalk.children Hne hIf hU0 .done)

end proof

end Perennial
