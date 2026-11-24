/-
The proof of `strings.Count`.
-/
module

public import Perennial.Spec.strings.Count
public import Perennial.Spec.strings.Index
public import Perennial.Spec.internal.bytealg.CountString
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

set_option maxHeartbeats 1000000 in
theorem strings.Count.wp_proof
    (wp_CountString : internal.bytealg.CountString.spec (GF := GF) (hG := hG))
    (wp_Index : strings.Index.spec (GF := GF) (hG := hG)) :
    strings.Count.spec (GF := GF) (hG := hG) := by
  intro s substr Hsub
  have Hsub0 : 0 < substr.length := List.length_pos_iff.mpr Hsub
  wp_start as #Hinit
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl0
  wp_if_destruct
  · exfalso; revert Hif; simp only [intoVal_eq_iff]; word
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  wp_if_destruct
  · -- one byte: `bytealg.CountString(s, substr[0])`
    obtain ⟨c, rfl⟩ : ∃ c, substr = [c] := by
      have h1 : substr.length = 1 := by revert Hif; simp only [intoVal_eq_iff]; word
      match substr, h1 with
      | [c], _ => exact ⟨c, rfl⟩
    try wp_auto
    wp_apply wp_CountString as %-
    try wp_auto
    rw [split_length_single]
    simp only [Nat.add_sub_cancel]
    iapply HΦ
    itrivial
  · -- the loop over `Index`
    ihave HI : (∃ (s' : GoString) (k : Nat), "s" ∷ s_ptr ↦ s' ∗ "n" ∷ n_ptr ↦ W64 (k : Int) ∗
        "%Hk" ∷ ⌜k + (split s' substr).length = (split s substr).length⌝ : IProp GF) $$ [s n]
    · iexists s, 0
      iframe s n
      ipureintro; omega
    wp_for HI
    wp_apply wp_Index as %Hsl
    have Hsl' := Hsl Hsub
    have Hb := internal.bytealg.index_bounds s' substr
    rw [split_index s' substr Hsub] at Hk
    wp_if_destruct
    · -- not found
      have Hm : internal.bytealg.index s' substr = -1 := by
        revert Hif; simp only [intoVal_eq_iff]; intro Hif; clear Hk; word
      rw [Hm, if_neg (by omega)] at Hk
      try wp_auto
      wp_for_post
      rw [show (split s substr).length - 1 = k by simp at Hk; omega]
      iapply HΦ
      itrivial
    · -- found at `m`: count it, and go on after it
      have Hm : 0 ≤ internal.bytealg.index s' substr := by
        have : internal.bytealg.index s' substr ≠ -1 := fun h => Hif (by rw [h])
        omega
      rw [if_pos Hm] at Hk
      have Hend := Hb.2 Hm
      obtain ⟨m, Hmeq⟩ : ∃ m : Nat, internal.bytealg.index s' substr = m :=
        ⟨_, (Int.toNat_of_nonneg Hm).symm⟩
      rw [Hmeq] at Hk Hend ⊢
      simp only [Int.toNat_natCast, List.length_cons] at Hk
      try wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      try wp_auto
      done

end proof

end Perennial
