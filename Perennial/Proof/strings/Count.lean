/-
The proof of `strings.Count`.
-/
module

public import Perennial.Spec.strings.Count
public import Perennial.Spec.strings.Index
public import Perennial.Spec.internal.bytealg.CountString
public import Perennial.Spec.unicode.utf8.RuneCountInString

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

theorem strings.Count.wp_proof
    (wp_Index : strings.Index.spec (GF := GF) (hG := hG))
    (wp_CountString : internal.bytealg.CountString.spec (GF := GF) (hG := hG))
    (wp_RuneCountInString : unicode.utf8.RuneCountInString.spec (GF := GF) (hG := hG)) :
    strings.Count.spec (GF := GF) (hG := hG) := by
  intro s substr
  wp_start as #Hinit
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl0
  wp_if_destruct
  · have hsub : substr = [] := List.eq_nil_of_length_eq_zero (by revert Hif; word)
    wp_apply wp_RuneCountInString
    rw [show W64 ((strings.count s substr : Nat) : Int) = W64 ((go.runes s).length : Int) + W64 1 by
      unfold strings.count; rw [if_pos hsub]; word]
    iapply HΦ
    itrivial
  have H0 := Hif
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl1
  wp_if_destruct
  · obtain ⟨c, rfl⟩ : ∃ c, substr = [c] := by
      have : substr.length = 1 := by revert Hif; word
      match substr, this with
      | [c], _ => exact ⟨c, rfl⟩
    simp only [List.getElem?_cons_zero]
    wp_apply wp_CountString as %-
    rw [show strings.count s [c] = s.count c by
      unfold strings.count; rw [if_neg (List.cons_ne_nil _ _)]
      exact strings.countOcc_single c _ s (Nat.le_refl _)]
    iapply HΦ
    itrivial
  have hsub : substr ≠ [] := fun h => by subst h; apply H0; rfl
  have hslen : 0 < substr.length := by cases substr <;> simp_all
  rw [show strings.count s substr = strings.countOcc s substr by
    unfold strings.count; rw [if_neg hsub]]
  ihave HI : (∃ (t : GoString) (m : Nat), "s" ∷ s_ptr ↦ t ∗ "n" ∷ n_ptr ↦ W64 (m : Int) ∗
      "%Ht" ∷ ⌜m + strings.countOcc t substr = strings.countOcc s substr⌝ : IProp GF) $$ [s n]
  · iexists s, 0
    iframe s n
    ipureintro; omega
  wp_for HI
  wp_apply wp_Index as %Hl
  have hb := internal.bytealg.index_bounds t substr
  have Hl := Hl hsub
  wp_if_destruct
  · have hnf : ¬ 0 ≤ internal.bytealg.index t substr := by
      intro h; have := hb.2 h; revert Hif; word
    rw [strings.countOcc_not_found t substr hnf, Nat.add_zero] at Ht
    wp_for_post
    rw [← Ht]
    iapply HΦ
    itrivial
  · have hf : 0 ≤ internal.bytealg.index t substr := by
      refine Classical.byContradiction fun h => Hif ?_
      have : internal.bytealg.index t substr = -1 := by omega
      rw [this]
    have hle := hb.2 hf
    rw [strings.countOcc_found t substr hsub hf] at Ht
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    have hlo : sint.Z (W64 (internal.bytealg.index t substr) + W64 (substr.length : Int)) =
        internal.bytealg.index t substr + substr.length := by word
    have hhi : sint.Z (W64 (t.length : Int)) = t.length := by word
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [hlo, hhi]; omega))]
    have hdrop : List.take (sint.nat (W64 (t.length : Int)) -
          sint.nat (W64 (internal.bytealg.index t substr) + W64 (substr.length : Int)))
        (List.drop (sint.nat (W64 (internal.bytealg.index t substr) + W64 (substr.length : Int))) t) =
        t.drop ((internal.bytealg.index t substr).toNat + substr.length) := by
      have h1 : sint.nat (W64 (internal.bytealg.index t substr) + W64 (substr.length : Int)) =
          (internal.bytealg.index t substr).toNat + substr.length := by
        rw [show sint.nat (W64 (internal.bytealg.index t substr) + W64 (substr.length : Int)) =
          (sint.Z (W64 (internal.bytealg.index t substr) + W64 (substr.length : Int))).toNat from rfl, hlo]
        omega
      rw [h1, List.take_of_length_le]
      simp only [List.length_drop]
      rw [show sint.nat (W64 (t.length : Int)) = (sint.Z (W64 (t.length : Int))).toNat from rfl, hhi]
      omega
    rw [hdrop]
    wp_auto
    wp_for_post
    iframe
    iexists _, (m + 1)
    iframe
    isplitl [n]
    · rw [show W64 (((m + 1 : Nat) : Int)) = W64 (m : Int) + W64 1 by word]
      iexact n
    ipureintro; omega

end proof

end Perennial
