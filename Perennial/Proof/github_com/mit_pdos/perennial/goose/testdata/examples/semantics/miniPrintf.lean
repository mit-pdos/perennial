/-
The proof of `miniPrintf` (a goose semantics test, `labels.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.miniPrintf

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE


set_option hygiene false in
macro "cleanup_cond" : tactic => `(tactic| simp only [_root_.decide_true, ite_true, hft, decide_false, Bool.false_eq_true, ite_false])

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.miniPrintf.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.miniPrintf.spec (GF := GF) (hG := hG) := by
  have hft : (#false : val) ≠ #true := fun h => absurd (GoGlobalContext.intoVal_inj_bool h) (by decide)
  wp_start
  wp_auto
  wp_func_call
  wp_call
  wp_auto
  ihave HI : (∃ (i : w64) (sl : GoSlice) (bs : List w8) (fl : w64),
      "i" ∷ i_ptr ↦ i ∗
      "out" ∷ out_ptr ↦ sl ∗
      "Hsl" ∷ sl ↦* bs ∗
      "Hcap" ∷ ownSliceCap w8 sl (DFrac.own 1) ∗
      "flags" ∷ flags_ptr ↦ fl ∗
      "Hend" ∷ end_ptr ↦ W64 9 ∗
      "%Hst" ∷ ⌜(i = W64 0 ∧ bs = [] ∧ fl = W64 0) ∨ (i = W64 4 ∧ bs = go!"xV" ∧ fl = W64 1) ∨
        (i = W64 6 ∧ bs = go!"xVy!" ∧ fl = W64 1) ∨ (i = W64 9 ∧ bs = go!"xVy!3z!" ∧ fl = W64 1)⌝
      : IProp GF) $$ [i out flags «end»]
  · iexists _, slice.nil, [], _
    iframe
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    ipureintro; left; exact ⟨rfl, rfl, rfl⟩
  wp_for HI
  rcases Hst with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · rw [if_pos (by decide)]
    wp_auto
    ihave HS : (∃ j : w64, "i" ∷ i_ptr ↦ j ∗ "%Hj" ∷ ⌜j = W64 0 ∨ j = W64 1⌝ : IProp GF) $$ [i]
    · iexists _; iframe; ipureintro; decide
    wp_for HS
    rcases Hj with rfl | rfl
    · wp_auto
      cleanup_cond
      wp_auto
      wp_for_post
      iframe
      iexists _
      iframe
      ipureintro; decide
    · wp_auto
      cleanup_cond
      wp_auto
      wp_apply wp_string_to_bytes as %sl2 ⟨Hsl2, -⟩
      wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl2] as %sl' ⟨Hsl, Hcap, -⟩
      ihave HF : (∃ (j : w64) (sl : GoSlice) (bs : List w8) (fl : w64),
          "i" ∷ i_ptr ↦ j ∗ "out" ∷ out_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* bs ∗
          "Hcap" ∷ ownSliceCap w8 sl (DFrac.own 1) ∗ "flags" ∷ flags_ptr ↦ fl ∗
          "%Hst" ∷ ⌜(j = W64 2 ∧ bs = go!"x" ∧ fl = W64 0) ∨ (j = W64 3 ∧ bs = go!"x" ∧ fl = W64 1)⌝
          : IProp GF) $$ [i out Hsl Hcap flags]
      · iexists _, _, _, _
        iframe
        ipureintro; decide
      wp_for HF
      rcases Hst with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · rw [if_pos (by decide)]
        wp_auto
        wp_for_post
        iframe
        iexists _, _, _, _
        iframe
        ipureintro; decide
      · rw [if_pos (by decide)]
        wp_auto
        wp_apply wp_slice_literal (V := w8) [(118#8 - W8 97 + W8 65 : w8)]
        isplitr
        · ipureintro; rfl
        iintro %sl2 ⟨Hsl2, -⟩
        wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl2] as %sl' ⟨Hsl, Hcap, -⟩
        wp_for_post
        wp_for_post
        iframe
        iexists _, _, _, _
        iframe
        ipureintro; decide
  · rw [if_pos (by decide)]
    wp_auto
    ihave HS : (∃ j : w64, "i" ∷ i_ptr ↦ j ∗ "%Hj" ∷ ⌜j = W64 4 ∨ j = W64 5⌝ : IProp GF) $$ [i]
    · iexists _; iframe; ipureintro; decide
    wp_for HS
    rcases Hj with rfl | rfl
    · wp_auto
      cleanup_cond
      wp_auto
      wp_for_post
      iframe
      iexists _
      iframe
      ipureintro; decide
    · wp_auto
      cleanup_cond
      wp_auto
      wp_apply wp_string_to_bytes as %sl2 ⟨Hsl2, -⟩
      wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl2] as %sl' ⟨Hsl, Hcap, -⟩
      ihave HF : (∃ (j : w64) (sl : GoSlice) (bs : List w8) (fl : w64),
          "i" ∷ i_ptr ↦ j ∗ "out" ∷ out_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* bs ∗
          "Hcap" ∷ ownSliceCap w8 sl (DFrac.own 1) ∗ "flags" ∷ flags_ptr ↦ fl ∗
          "%Hst" ∷ ⌜j = W64 6 ∧ bs = go!"xVy" ∧ fl = W64 1⌝
          : IProp GF) $$ [i out Hsl Hcap flags]
      · iexists _, _, _, _
        iframe
        ipureintro; decide
      wp_for HF
      obtain ⟨rfl, rfl, rfl⟩ := Hst
      rw [if_pos (by decide)]
      wp_auto
      wp_for_post
      wp_apply wp_slice_literal (V := w8) [W8 33]
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl2] as %sl' ⟨Hsl, Hcap, -⟩
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro; decide
  · rw [if_pos (by decide)]
    wp_auto
    ihave HS : (∃ j : w64, "i" ∷ i_ptr ↦ j ∗ "%Hj" ∷ ⌜j = W64 6 ∨ j = W64 7 ∨ j = W64 8⌝ : IProp GF) $$ [i]
    · iexists _; iframe; ipureintro; decide
    wp_for HS
    rcases Hj with rfl | rfl | rfl
    · wp_auto
      cleanup_cond
      wp_auto
      wp_for_post
      iframe
      iexists _
      iframe
      ipureintro; decide
    · wp_auto
      cleanup_cond
      wp_auto
      wp_for_post
      iframe
      iexists _
      iframe
      ipureintro; decide
    · wp_auto
      cleanup_cond
      wp_auto
      wp_apply wp_string_to_bytes as %sl2 ⟨Hsl2, -⟩
      wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl2] as %sl' ⟨Hsl, Hcap, -⟩
      ihave HF : (∃ (j : w64) (sl : GoSlice) (bs : List w8) (fl : w64),
          "i" ∷ i_ptr ↦ j ∗ "out" ∷ out_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* bs ∗
          "Hcap" ∷ ownSliceCap w8 sl (DFrac.own 1) ∗ "flags" ∷ flags_ptr ↦ fl ∗
          "%Hst" ∷ ⌜j = W64 9 ∧ bs = go!"xVy!3z" ∧ fl = W64 1⌝
          : IProp GF) $$ [i out Hsl Hcap flags]
      · iexists _, _, _, _
        iframe
        ipureintro; decide
      wp_for HF
      obtain ⟨rfl, rfl, rfl⟩ := Hst
      rw [if_neg (by decide)]
      rw [if_neg (by decide)]
      wp_auto
      wp_apply wp_slice_literal (V := w8) [W8 33]
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl2] as %sl' ⟨Hsl, Hcap, -⟩
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro; decide
  · rw [if_neg (by decide)]
    rw [if_neg (by decide)]
    wp_auto
    wp_apply wp_bytes_to_string $$ Hsl as Hsl
    iapply HΦ
    iexact Hpre

end proof

end Perennial
