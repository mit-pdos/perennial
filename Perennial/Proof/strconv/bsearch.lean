/-
The proof of `strconv.bsearch`.
-/
module

public import Perennial.Spec.strconv.bsearch

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strconv.Assumptions]

theorem strconv.bsearch.wp_proof : strconv.bsearch.spec (GF := GF) (hG := hG) := by
  constructor
  · intro s xs v dq
    wp_start as Hs
    ihave %Hlen := ownSlice_len _ _ _ $$ Hs
    have hlenZ : sint.Z s.len = xs.length := by
      obtain ⟨h1, h2⟩ := Hlen; simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
    wp_auto
    ihave HI : (∃ i j : w64,
        "i" ∷ i_ptr ↦ i ∗
        "j" ∷ j_ptr ↦ j ∗
        "Hs" ∷ s ↦*{dq} xs ∗
        "%Hij" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len⌝ : IProp GF)
        $$ [i j Hs]
    · iexists (W64 0), s.len
      iframe
      ipureintro; refine ⟨by decide, by word, Int.le_refl _⟩
    wp_for HI
    wp_if_destruct
    · have hc : sint.Z i < sint.Z j := by
        first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
      have hh : sint.Z (i + BitVec.sshiftRight' (j - i) (W64 1)) =
          sint.Z i + (sint.Z j - sint.Z i) / 2 := strconv.bsearch_mid i j (by omega) (by omega)
      rw [ite_eq_left (by rw [hh]; omega)]
      obtain ⟨x, hx⟩ : ∃ x, xs[(sint.Z (i + BitVec.sshiftRight' (j - i) (W64 1))).toNat]? = some x :=
        ⟨_, List.getElem?_eq_getElem (by rw [hh]; omega)⟩
      wp_apply wp_load_slice_index _ _ _ _ x (by rw [hh]; omega) $$ [$Hs] as Hs
      · ipureintro; exact hx
      wp_if_destruct
      · wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro; refine ⟨by word, by word, by word⟩
      · wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro; refine ⟨by word, by word, by word⟩
    · have hc : ¬ sint.Z i < sint.Z j := by
        first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
      try simp only [decide_eq_false hc, decide_true, ↓reduceIte]
      try wp_auto
      wp_if_destruct
      · rw [ite_eq_left (by omega)]
        obtain ⟨x, hx⟩ : ∃ x, xs[(sint.Z i).toNat]? = some x :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        wp_apply wp_load_slice_index _ _ _ _ x (by omega) $$ [$Hs] as Hs
        · ipureintro; exact hx
        iapply HΦ
        iframe
        ipureintro; omega
      · iapply HΦ
        iframe
        ipureintro; omega
  · intro s xs v dq
    wp_start as Hs
    ihave %Hlen := ownSlice_len _ _ _ $$ Hs
    have hlenZ : sint.Z s.len = xs.length := by
      obtain ⟨h1, h2⟩ := Hlen; simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
    wp_auto
    ihave HI : (∃ i j : w64,
        "i" ∷ i_ptr ↦ i ∗
        "j" ∷ j_ptr ↦ j ∗
        "Hs" ∷ s ↦*{dq} xs ∗
        "%Hij" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len⌝ : IProp GF)
        $$ [i j Hs]
    · iexists (W64 0), s.len
      iframe
      ipureintro; refine ⟨by decide, by word, Int.le_refl _⟩
    wp_for HI
    wp_if_destruct
    · have hc : sint.Z i < sint.Z j := by
        first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
      have hh : sint.Z (i + BitVec.sshiftRight' (j - i) (W64 1)) =
          sint.Z i + (sint.Z j - sint.Z i) / 2 := strconv.bsearch_mid i j (by omega) (by omega)
      rw [ite_eq_left (by rw [hh]; omega)]
      obtain ⟨x, hx⟩ : ∃ x, xs[(sint.Z (i + BitVec.sshiftRight' (j - i) (W64 1))).toNat]? = some x :=
        ⟨_, List.getElem?_eq_getElem (by rw [hh]; omega)⟩
      wp_apply wp_load_slice_index _ _ _ _ x (by rw [hh]; omega) $$ [$Hs] as Hs
      · ipureintro; exact hx
      wp_if_destruct
      · wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro; refine ⟨by word, by word, by word⟩
      · wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro; refine ⟨by word, by word, by word⟩
    · have hc : ¬ sint.Z i < sint.Z j := by
        first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
      try simp only [decide_eq_false hc, decide_true, ↓reduceIte]
      try wp_auto
      wp_if_destruct
      · rw [ite_eq_left (by omega)]
        obtain ⟨x, hx⟩ : ∃ x, xs[(sint.Z i).toNat]? = some x :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        wp_apply wp_load_slice_index _ _ _ _ x (by omega) $$ [$Hs] as Hs
        · ipureintro; exact hx
        iapply HΦ
        iframe
        ipureintro; omega
      · iapply HΦ
        iframe
        ipureintro; omega

end proof

end Perennial
