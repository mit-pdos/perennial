/-
The proof of `errors.asType`.
-/
module

public import Perennial.Spec.errors.asType_

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
theorem errors.asType.wp_proof :
    errors.asType.spec (GF := GF) (hG := hG) := by
  intro S err ppe pe T' _ _ T _
  iloeb as IH generalizing %err %pe
  irevert IH
  iapply asTypeHide_intro
  iintro #IH
  wp_start as H
  iNamed H
  wp_alloc r1 as Hr1
  wp_auto
  wp_alloc r2 as Hr2
  wp_auto
  iclear Hr1 Hr2
  ihave HI : (∃ (e : GoError) (pe' : Loc),
      "err" ∷ err_ptr ↦ e ∗ "%HSe" ∷ ⌜S e⌝ ∗ "Hppe" ∷ ppe ↦ pe' ∗
      "Hpe" ∷ (⌜pe' = Loc.null⌝ ∨ ∃ v : T', pe' ↦ v) :
      IProp GF) $$ [err Hppe Hpe]
  · iexists err, pe
    iframe
    ipureintro; exact HS
  wp_for HI
  haveI : T ↓u underlying T := ⟨rfl⟩
  wp_auto
  cases e with
  | nil =>
    dsimp only
    wp_auto
    wp_for_post
    iapply HΦ
    iframe
  | ok ii =>
    ihave Hnode := Htree $$ %ii %HSe
    iNamed Hnode
    dsimp only
    obtain ⟨x, hx⟩ := asTypeTyped_val Htyped
    rw [hx]
    generalize (if go.isInterfaceType (underlying T) = true then go.typeSetContains ii.ty T
      else decide (ii.ty = T)) = b
    cases b
    case true =>
      wp_auto
      wp_for_post
      iapply HΦ
      iframe
    wp_store; wp_pures; wp_store; wp_pures; wp_load; wp_pures
    -- the `As` statement, joined before the `Unwrap` switch: it either returns
    -- or falls through with an updated `*ppe`
    wp_join (Q := fun v => iprop(
        (⌜v = executeVal⌝ ∗ ∃ q : Loc, "ppe" ∷ ppe_ptr ↦ ppe ∗ "err" ∷ err_ptr ↦ interface.ok ii ∗
          "Hppe" ∷ ppe ↦ q ∗ "Hpe" ∷ (⌜q = Loc.null⌝ ∨ ∃ v : T', q ↦ v)) ∨
        (∃ (e : T') (q : Loc), ⌜v = returnVal (PairV #e #true)⌝ ∗ ppe ↦ q ∗
          (⌜q = Loc.null⌝ ∨ ∃ v : T', q ↦ v)))) at next with [ppe err Hppe Hpe]
    wp_auto
    have hu : underlying (go.InterfaceType [go.MethodElem go!"As" (go.Signature [go.any] false [go.bool])]) =
        go.InterfaceType [go.MethodElem go!"As" (go.Signature [go.any] false [go.bool])] :=
      go.is_underlying
    cases hAs : go.typeSetContains ii.ty
      (go.InterfaceType [go.MethodElem go!"As" (go.Signature [go.any] false [go.bool])])
    case' true =>
      simp only [go.typeSetContains, hu, go.typeSetElemsContains, go.typeSetElemContains,
        List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq] at hAs
      simp only [hAs, ↓reduceIte]
      wp_auto
      by_cases hnull : pe' = Loc.null
      case' pos =>
        subst hnull
        wp_auto
        iclear Hpe
        wp_apply HAs $$ [$«$r0»] as %b %v' Hv
        cases b
        case true =>
          wp_auto
          iright; iexists _, _; iframe; ipureintro; rfl
        wp_auto
        ihave Hpe : (⌜«$r0_ptr» = Loc.null⌝ ∨ ∃ v : T', «$r0_ptr» ↦ v : IProp GF) $$ [Hv]
        · iright; iexists _; iexact Hv
        ileft; iframe; ipureintro; rfl
      case' neg =>
        icases Hpe with (%h | ⟨%v, Hv⟩)
        · exact absurd h hnull
        simp only [hnull, decide_false]
        wp_auto
        wp_apply HAs $$ [$Hv] as %b %v' Hv
        cases b
        case true =>
          wp_auto
          iright; iexists _, _; iframe; ipureintro; rfl
        wp_auto
        ihave Hpe : (⌜pe' = Loc.null⌝ ∨ ∃ v : T', pe' ↦ v : IProp GF) $$ [Hv]
        · iright; iexists _; iexact Hv
        ileft; iframe; ipureintro; rfl
    case' false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      ileft; iframe; ipureintro; rfl
    iintro HQ
    icases HQ with (⟨%Hv, %pe', ppe, err, Hppe, Hpe⟩ | ⟨%e0, %q, %Hv, Hppe, Hpe⟩)
    rotate_left
    · subst Hv
      wp_auto
      wp_for_post
      iapply HΦ
      iframe
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
        iframe
      | ok ii' =>
        wp_auto
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        exact HSe'
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
        ihave HI2 : (∃ (j : w64) (q : Loc) (e2 : GoError),
            "i" ∷ i_ptr ↦ j ∗ "Hs" ∷ s ↦*{dq} es ∗ "err" ∷ err_ptr ↦ e2 ∗
            "Hppe" ∷ ppe ↦ q ∗ "Hpe" ∷ (⌜q = Loc.null⌝ ∨ ∃ v : T', q ↦ v) ∗
            "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len⌝ : IProp GF) $$ [i Hs err Hppe Hpe]
        · iexists W64 0, _, _
          iframe
          ipureintro; word
        wp_for HI2
        wp_if_destruct
        · simp only [Hj.1, Hif, _root_.and_self, ↓reduceIte]
          list_elem es (sint.nat j) as e2'
          wp_apply wp_load_slice_index s (sint.Z j) es dq e2' Hj.1 $$ [Hs] with Hs
          · iframe; ipureintro; exact He2'_lookup
          have HSe2' : S e2' := Hes e2' (List.mem_of_getElem? He2'_lookup)
          cases e2' with
          | nil =>
            wp_auto
            wp_for_post
            iframe
            iexists j + W64 1, _, _
            iframe
            ipureintro; word
          | ok ii2 =>
            irevert IH
            iapply asTypeHide_elim
            iintro #IH
            wp_auto
            wp_apply IH $$ %(interface.ok ii2) %q [Hppe Hpe] as %x0 %ok0 %q' ⟨Hppe, Hpe⟩
            · iframe; iframe #; ipureintro; exact HSe2'
            cases ok0
            case true =>
              wp_auto
              wp_for_post
              wp_for_post
              iapply HΦ
              iframe
            case false =>
              wp_auto
              wp_for_post
              iframe
              iexists j + W64 1, _, _
              iframe
              ipureintro; word
        · wp_for_post
          iapply HΦ
          iframe
      case false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        wp_auto
        wp_for_post
        iapply HΦ
        iframe

end proof

end Perennial
