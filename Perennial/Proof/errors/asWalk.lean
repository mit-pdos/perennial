/-
The proof of `errors.asWalk` (the tree walk of the model of `As`).
-/
module

public import Perennial.Spec.errors.asWalk
public import Perennial.Spec.errors.asAssign

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace errors

/-- An error not assignable to `T` needs no typing of its stored value. -/
theorem asTypeTyped_of_not_assignable [GooseExts] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions]
    {T' : Type} {T : go.GoType} {ii : GoInterfaceOk} (h : asAssignable T ii = false) :
    AsTypeTyped T' T ii := by
  unfold AsTypeTyped
  unfold asAssignable at h
  split
  · rename_i hI
    simp only [hI, ↓reduceIte] at h
    intro h'; rw [h] at h'; cases h'
  · rename_i hI
    simp only [hI, Bool.false_eq_true, ↓reduceIte, decide_eq_false_iff_not] at h
    intro h'; exact absurd h' h

end errors

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : errors.Assumptions]

/-- Whether a type has the one method of a one-method interface. -/
theorem errors.typeSetContains_method
    (t : go.GoType) (m : GoString) (sig : go.signature) :
    go.typeSetContains t (go.InterfaceType [go.MethodElem m sig]) =
      decide (methodSet t !! m = some sig) := by
  have hu : underlying (go.InterfaceType [go.MethodElem m sig]) =
      go.InterfaceType [go.MethodElem m sig] := go.is_underlying
  simp [go.typeSetContains, hu, go.typeSetElemsContains, go.typeSetElemContains]

theorem errors.asWalk.wp_proof
    (wp_asAssign : errors.asAssign.spec (GF := GF) (hG := hG)) :
    errors.asWalk.spec (GF := GF) (hG := hG) := by
  refine ⟨?_, ?_, ?_⟩
  · intro S ii l T' _ _ T _ v hT hdec
    iloeb as IH generalizing %ii %v
    irevert IH
    iapply asTypeHide_intro
    iintro #IH
    wp_start as ⟨#Htree, %HS, Hl⟩
    wp_auto
    ihave HI : iprop(∃ (ii' : GoInterfaceOk) (v' : T'),
        "err" ∷ err_ptr ↦ interface.ok ii' ∗ "%HS" ∷ ⌜S (interface.ok ii')⌝ ∗ "Hl" ∷ l ↦ v')
        $$ [err Hl]
    · iexists ii, v
      iframe
      ipureintro; exact HS
    wp_for HI
    ihave Hnode := Htree $$ %ii' %HS
    iNamed Hnode
    wp_apply wp_asAssign ii' l v' hT (hdec ii' HS) Htyped $$ [$Hl] as %v'' ⟨Hl, -⟩
    generalize asAssignable T ii' = b
    cases b
    case true =>
      wp_auto
      wp_for_post
      iapply HΦ
      iframe
    wp_auto
    rw [← apply_ite (intoVal (V := GoInterface))]
    wp_store; wp_pures; wp_store; wp_pures
    -- the `As` statement, joined before the `Unwrap` switch: it either returns or falls through
    wp_join (Q := fun r => iprop(
        (⌜r = executeVal⌝ ∗ ∃ v3 : T', "Hl" ∷ l ↦ v3 ∗
          "«$res0»" ∷ «$res0_ptr» ↦ zero_val Bool ∗
          "target" ∷ target_ptr ↦ interface.mkOk (go.PointerType T) #l) ∨
        (⌜r = returnVal #()⌝ ∗ ∃ v3 : T', l ↦ v3 ∗ «$res0_ptr» ↦ true))) at next
      with [Hl «$res0» ok x target]
    · cases hAs : go.typeSetContains ii'.ty (go.InterfaceType [go.MethodElem go!"As" (go.Signature [go.any] false [go.bool])])
      case true =>
        rw [errors.typeSetContains_method] at hAs
        simp only [decide_eq_true_eq] at hAs
        simp only [hAs, ↓reduceIte]
        wp_auto
        wp_apply HAs $$ [$Hl] as %b %v3 Hl
        cases b
        case true =>
          wp_auto
          iright; iframe; ipureintro; rfl
        wp_auto
        ileft; iframe; ipureintro; rfl
      simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      ileft; iframe; ipureintro; rfl
    iintro HQ
    icases HQ with (⟨%Hv, %v3, Hl, «$res0», target⟩ | ⟨%Hv, %v3, Hl, «$res0»⟩)
    rotate_left
    · subst Hv
      wp_auto
      wp_for_post
      iapply HΦ
      iframe
    subst Hv
    wp_auto
    cases hU : go.typeSetContains ii'.ty (go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])])
    case true =>
      rw [errors.typeSetContains_method] at hU
      simp only [decide_eq_true_eq] at hU
      simp only [hU, ↓reduceIte]
      wp_auto
      wp_apply HUnwrap as %e' %HSe'
      cases e' with
      | nil =>
        wp_auto
        wp_for_post
        iapply HΦ
        iframe
      | ok ii2 =>
        wp_auto
        wp_for_post
        iframe
        iexists ii2, v3
        iframe
        ipureintro
        exact HSe'
    rw [errors.typeSetContains_method] at hU
    simp only [decide_eq_false_iff_not] at hU
    simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto
    cases hU2 : go.typeSetContains ii'.ty (go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.GoType.SliceType go.error])])
    case true =>
      rw [errors.typeSetContains_method] at hU2
      simp only [decide_eq_true_eq] at hU2
      simp only [hU, ↓reduceIte]
      simp only [hU2, ↓reduceIte]
      wp_auto
      wp_apply HUnwrap as %s %dq %es ⟨Hs, %Hes⟩
      ihave %Hlen := ownSlice_len _ _ _ $$ Hs
      ihave HI2 : (∃ (j : w64) (v4 : T') (e2 : GoError),
          "i" ∷ i_ptr ↦ j ∗ "Hs" ∷ s ↦*{dq} es ∗ "err" ∷ err_ptr ↦ e2 ∗ "Hl" ∷ l ↦ v4 ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len⌝ : IProp GF) $$ [i Hs err Hl]
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
          wp_apply IH $$ %ii2 %v4 [Hl] as %b %v5 Hl
          · iframe; iframe #; ipureintro; exact HSe2'
          cases b
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
    simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto
    wp_for_post
    iapply HΦ
    iframe
  · intro ii l T' _ _ T _ v hT hdec hA htyped
    wp_start as Hl
    wp_auto
    ihave HI : iprop(err_ptr ↦ interface.ok ii ∗ l ↦ v) $$ [err Hl]
    · iframe
    wp_for HI
    icases HI with ⟨err, Hl⟩
    wp_auto
    wp_apply wp_asAssign ii l v hT hdec htyped $$ [$Hl]
      as %v' ⟨Hl, %Hv'⟩
    rw [hA]
    wp_auto
    wp_for_post
    iapply HΦ
    iframe
    ipureintro
    exact Hv'.1 hA
  · intro n ii l T' _ _ T _ v hT
    wp_start as ⟨Hl, Hm⟩
    wp_auto
    ihave HI : iprop(∃ (ii' : GoInterfaceOk) (k : Nat),
        err_ptr ↦ interface.ok ii' ∗ l ↦ v ∗ asNoMatch (GF := GF) T k (interface.ok ii'))
        $$ [err Hl Hm]
    · iexists ii, n
      iframe
    wp_for HI
    icases HI with ⟨err, Hl, Hm⟩
    ihave Hm' : iprop(⌜asNoMatchLeaf T (interface.ok ii')⌝ ∨ ∃ (k' : Nat) (ii2 : GoInterfaceOk),
        ⌜interface.ok ii' = interface.ok ii2 ∧ asAssignable T ii2 = false ∧ AsDecided T ii2 ∧
          methodSet ii2.ty !! go!"As" ≠ some (go.Signature [go.any] false [go.bool]) ∧
          methodSet ii2.ty !! go!"Unwrap" = some (go.Signature [] false [go.error])⌝ ∗
        ∀ Φ : val → IProp GF, (∀ e' : GoError, asNoMatch (GF := GF) T k' e' -∗ Φ #e') -∗
          WP (App (Val #(methods ii2.ty go!"Unwrap" ii2.v)) (Val #())) {{ Φ }}) $$ [Hm]
    · cases k with
      | zero => iunfold errors.asNoMatch at Hm; ileft; iexact Hm
      | succ k' =>
        iunfold errors.asNoMatch at Hm
        icases Hm with (%H | ⟨%ii2, %H, HW⟩)
        · ileft; ipureintro; exact H
        · iright; iexists k', ii2; iframe; ipureintro; exact H
    icases Hm' with (%Hleaf | ⟨%k', %ii2, %Hw, HW⟩)
    · rcases Hleaf with h | ⟨ii3, h, hleaf, hA, hdec⟩
      · cases h
      cases h
      wp_auto
      wp_apply wp_asAssign ii' l v hT hdec (errors.asTypeTyped_of_not_assignable hA) $$ [$Hl]
        as %v' ⟨Hl, %Hv'⟩
      rw [hA]
      obtain rfl := Hv'.2 hA
      wp_auto
      obtain ⟨hAs, hU1, hU2⟩ := hleaf
      have hAsF : go.typeSetContains ii'.ty (go.InterfaceType [go.MethodElem go!"As" (go.Signature [go.any] false [go.bool])]) = false := by
        rw [errors.typeSetContains_method]; simpa using hAs
      have hU1F : go.typeSetContains ii'.ty (go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])]) = false := by
        rw [errors.typeSetContains_method]; simpa using hU1
      have hU2F : go.typeSetContains ii'.ty
          (go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.GoType.SliceType go.error])]) = false := by
        rw [errors.typeSetContains_method]; simpa using hU2
      cases hc : go.typeSetContains ii'.ty (go.InterfaceType [go.MethodElem go!"As" (go.Signature [go.any] false [go.bool])])
      case true => exact absurd (hc.symm.trans hAsF) (by decide)
      simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      cases hc : go.typeSetContains ii'.ty (go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])])
      case true => exact absurd (hc.symm.trans hU1F) (by decide)
      simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      cases hc2 : go.typeSetContains ii'.ty (go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.GoType.SliceType go.error])])
      case true => exact absurd (hc2.symm.trans hU2F) (by decide)
      simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      wp_for_post
      iapply HΦ
      iexact Hl
    · obtain ⟨h, hA, hdec, hAs, hU⟩ := Hw
      cases h
      wp_auto
      wp_apply wp_asAssign ii' l v hT hdec (errors.asTypeTyped_of_not_assignable hA) $$ [$Hl]
        as %v' ⟨Hl, %Hv'⟩
      rw [hA]
      obtain rfl := Hv'.2 hA
      wp_auto
      have hAsF : go.typeSetContains ii'.ty (go.InterfaceType [go.MethodElem go!"As" (go.Signature [go.any] false [go.bool])]) = false := by
        rw [errors.typeSetContains_method]; simpa using hAs
      have hU1T : go.typeSetContains ii'.ty (go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])]) = true := by
        rw [errors.typeSetContains_method]; simpa using hU
      cases hc : go.typeSetContains ii'.ty (go.InterfaceType [go.MethodElem go!"As" (go.Signature [go.any] false [go.bool])])
      case true => exact absurd (hc.symm.trans hAsF) (by decide)
      simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      cases hc : go.typeSetContains ii'.ty (go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])])
      case false => exact absurd (hc.symm.trans hU1T) (by decide)
      simp only [↓reduceIte]
      wp_auto
      wp_bind (App (Val #(methods ii'.ty go!"Unwrap" ii'.v)) (Val #()))
      iapply HW
      iintro %e' He'
      wp_auto
      cases e' with
      | nil =>
        wp_auto
        wp_for_post
        iapply HΦ
        iexact Hl
      | ok ii2 =>
        wp_auto
        wp_for_post
        iframe
        iexists ii2, k'
        iframe

end proof

end Perennial
