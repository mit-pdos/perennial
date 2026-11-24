/-
The proof of `strings.IndexRune`.
-/
module

public import Perennial.Spec.strings.IndexRune
public import Perennial.Spec.strings.IndexByte
public import Perennial.Spec.strings.Index
public import Perennial.Spec.unicode.utf8.ValidRune

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

theorem strings.IndexRune.wp_proof
    (wp_IndexByte : strings.IndexByte.spec (GF := GF) (hG := hG))
    (wp_Index : strings.Index.spec (GF := GF) (hG := hG))
    (wp_ValidRune : unicode.utf8.ValidRune.spec (GF := GF) (hG := hG)) :
    strings.IndexRune.spec (GF := GF) (hG := hG) := by
  intro s r
  wp_start as #Hinit
  wp_auto
  have hT : ¬ (0 ≤ sint.Z r ∧ sint.Z r < 0x80) → strings.indexRune s r =
      if r = go.runeError then strings.runeErrorIndex s
      else if strings.validRune r then internal.bytealg.index s (go.runeString (sint.Z r))
      else -1 := fun h => by unfold strings.indexRune; simp only [h, ↓reduceIte]
  wp_if_destruct
  wp_if_destruct
  · have hA : 0 ≤ sint.Z r ∧ sint.Z r < 0x80 := by
      simp only [eq_comm (a := true), decide_eq_true_eq] at Hif; constructor <;> word
    wp_apply wp_IndexByte
    unfold strings.indexRune
    rw [ite_eq_left_of_eq_true _ _ (eq_true hA)]
    iapply HΦ
    itrivial
  all_goals
    have hA : ¬ (0 ≤ sint.Z r ∧ sint.Z r < 0x80) := by
      first
        | (simp only [eq_comm (a := true), decide_eq_true_eq] at Hif; intro h; apply Hif; word)
        | (intro h; apply Hif; word)
    rw [hT hA]
    clear hT
  all_goals
    wp_if_destruct
    · have hr : r = go.runeError := by
        simp only [eq_comm (a := true), decide_eq_true_eq] at Hif; exact Hif
      rw [ite_eq_left_of_eq_true _ _ (eq_true hr)]
      wp_apply (wp_string_for_range s _ (fun j => iprop(
          «$res0_ptr» ↦ zero_val w64 ∗ (∃ v : w32, r_ptr ↦ v) ∗ (∃ k : w64, i_ptr ↦ k) ∗
          (True -∗ Φ #(W64 (strings.runeErrorIndex s))) ∗
          ⌜∀ e ∈ (go.runes s).take j, e.2 ≠ go.runeError⌝))) $$ [«$res0» r i HΦ]
      · iframe
        ipureintro; simp
      · imodintro
        iintro %j %k %rv %hk ⟨Hres, ⟨%v, Hr⟩, ⟨%k0, Hi⟩, HΦ, %Hno⟩
        wp_auto
        have htake : (go.runes s).take (j + 1) = (go.runes s).take j ++ [(k, rv)] := by
          rw [List.take_add_one, hk]; rfl
        wp_if_destruct
        · iapply forRangePostcondition_return
          wp_auto
          rw [strings.runeErrorIndex_eq_of s j (k, W32 65533) hk (by rfl) Hno]
          iapply HΦ
          itrivial
        · iapply forRangePostcondition_do
          iframe
          ipureintro
          rw [htake]
          intro e he
          rcases List.mem_append.1 he with he | he
          · exact Hno e he
          · rw [List.mem_singleton.1 he]; exact Hif
      · iintro ⟨Hres, Hr, Hi, HΦ, %Hno⟩
        wp_auto
        rw [List.take_length] at Hno
        rw [strings.runeErrorIndex_eq_neg s Hno]
        iapply HΦ
        itrivial
    · have hr : ¬ r = go.runeError := by
        simp only [eq_comm (a := true), decide_eq_true_eq] at Hif; exact Hif
      simp only [hr, ↓reduceIte]
      wp_apply wp_ValidRune as %b %Hb
      wp_if_destruct
      · have hv : ¬ strings.validRune r := by
          unfold strings.validRune; intro h; simp_all <;> omega
        simp only [hv, ↓reduceIte]
        iapply HΦ
        itrivial
      · have hv : strings.validRune r := by
          unfold strings.validRune; simp_all
        rw [ite_eq_left_of_eq_true _ _ (eq_true hv)]
        wp_apply wp_Index as %-
        iapply HΦ
        itrivial

end proof

end Perennial
