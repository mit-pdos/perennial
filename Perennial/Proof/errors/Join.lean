/-
The proof of `errors.Join`.
-/
module

public import Perennial.Spec.errors.Join

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

theorem errors.Join.wp_proof :
    errors.Join.spec (GF := GF) (hG := hG) := by
  intro sl dq es
  wp_start as Hs
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hs
  ihave IH : iprop(∃ (i n : w64) (ev : GoInterface),
      "i" ∷ i_ptr ↦ i ∗
      "n" ∷ n_ptr ↦ n ∗
      "err" ∷ err_ptr ↦ ev ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ (es.length : Int)⌝ ∗
      "%Hn" ∷ ⌜sint.Z n = ((es.take (sint.Z i).toNat).filter (· ≠ interface.nil)).length⌝)
      $$ [i n err]
  · iexists _, _, _
    iframe
    ipureintro
    exact ⟨⟨by word, by word⟩, by simp⟩
  wp_for IH
  split
  · rename_i Hif
    replace Hif := of_decide_eq_true Hif
    have Hlt : (sint.Z i).toNat < es.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, es[(sint.Z i).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    wp_auto
    rw [ite_eq_left ⟨Hi.1, Hif⟩]
    wp_apply wp_load_slice_index sl (sint.Z i) es dq x Hi.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hx
    have hnle : ((es.take (sint.Z i).toNat).filter (· ≠ interface.nil)).length ≤ (sint.Z i).toNat :=
      Nat.le_trans (List.length_filter_le _ _) (List.length_take_le _ _)
    have Hsucc : (sint.Z (i + W64 1)).toNat = (sint.Z i).toNat + 1 := by word
    rcases x with _ | xi
    · wp_auto
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro
      have hL : ((es.take (sint.Z i).toNat).filter (· ≠ interface.nil)).length + 1 < 2 ^ 63 := by
        word
      have hn1 : sint.Z (n + W64 1) = sint.Z n + 1 := by word
      refine ⟨⟨by word, by word⟩, ?_⟩
      rw [hn1, Hn, Hsucc, List.take_add_one, Hx]
      simp [List.filter_append]
    · wp_auto
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ?_⟩
      rw [Hsucc, List.take_add_one, Hx]
      simp [List.filter_append, Hn]
  · rename_i Hif
    replace Hif : ¬ sint.Z i < sint.Z sl.len := fun h => Hif (decide_eq_true h)
    have Hall : (sint.Z i).toNat = es.length := by word
    rw [Hall, List.take_length] at Hn
    wp_auto
    wp_if_destruct
    · iapply HΦ
      iframe
      ipureintro
      have h0 : (es.filter (· ≠ interface.nil)).length = 0 := by word
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at h0
      simp only [true_iff]
      intro x hx
      simpa using h0 x hx
    have Hpos : 0 < sint.Z n := by
      have : sint.Z n ≠ 0 := fun h => Hif (by word)
      omega
    wp_apply wp_slice_make3 (V := GoInterface) (W64 0) n ⟨by word, by word⟩ as %sl0 ⟨Hsl0, Hcap0, -⟩
    icases typedPointsto_split _ _ _ $$ «$r0» with «$r0»
    simp only [TypedPointsto.typedPointstoDef]
    icases «$r0» with ⟨errs, -⟩
    ihave IH : iprop(∃ (i : w64) (ev : GoInterface) (sl1 : GoSlice) (acc : List GoInterface),
        "i" ∷ i_ptr ↦ i ∗
        "err" ∷ err_ptr ↦ ev ∗
        "r" ∷ «$r0_ptr».[errors.joinError, go!"errs"] ↦ sl1 ∗
        "Hsl1" ∷ sl1 ↦* acc ∗
        "Hcap1" ∷ ownSliceCap GoInterface sl1 (DFrac.own 1) ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ (es.length : Int)⌝) $$ [i err errs Hsl0 Hcap0]
    · iexists _, _, _, _
      iframe
      ipureintro
      exact ⟨by word, by word⟩
    wp_for IH
    split
    · rename_i Hif
      replace Hif := of_decide_eq_true Hif
      have Hlt : (sint.Z i).toNat < es.length := by word
      obtain ⟨x, Hx⟩ : ∃ x, es[(sint.Z i).toNat]? = some x :=
        ⟨_, List.getElem?_eq_getElem Hlt⟩
      wp_auto
      rw [ite_eq_left ⟨Hi.1, Hif⟩]
      wp_apply wp_load_slice_index sl (sint.Z i) es dq x Hi.1 $$ [Hs] as Hs
      · iframe; ipureintro; exact Hx
      have Hsucc : (sint.Z (i + W64 1)).toNat = (sint.Z i).toNat + 1 := by word
      rcases x with xi | _
      · wp_auto
        wp_apply wp_slice_literal (V := GoInterface) [GoInterface.ok xi]
        isplitr
        · ipureintro; rfl
        iintro %sl2 ⟨Hsl2, -⟩
        wp_apply wp_slice_append $$ [$Hsl1 $Hcap1 $Hsl2] as %sl' ⟨Hsl1, Hcap1, -⟩
        wp_for_post
        iframe
        iexists _, _, _, _
        iframe
        ipureintro
        exact ⟨by word, by word⟩
      · wp_auto
        wp_for_post
        iframe
        iexists _, _, _, _
        iframe
        ipureintro
        exact ⟨by word, by word⟩
    · wp_auto
      iapply HΦ
      iframe
      ipureintro
      constructor
      · intro h
        simp [interface.mkOk] at h
      · intro hall
        exfalso
        have h0 : es.filter (· ≠ interface.nil) = [] :=
          List.filter_eq_nil_iff.2 (fun x hx => by simpa using hall x hx)
        rw [h0] at Hn
        simp at Hn
        omega

end proof

end Perennial
