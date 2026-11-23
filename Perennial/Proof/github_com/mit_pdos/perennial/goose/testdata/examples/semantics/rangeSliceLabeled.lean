/-
The proof of `rangeSliceLabeled` (a goose semantics test, `labels.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.rangeSliceLabeled

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.rangeSliceLabeled.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.rangeSliceLabeled.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply wp_slice_literal (V := w64) [W64 2, W64 3, W64 4, W64 0, W64 8]
  isplitr
  · ipureintro; rfl
  iintro %sl_ptr ⟨Hsl, -⟩
  generalize hsl : slice.mk sl_ptr _ _ = sl
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  ihave HI : (∃ i sum xv : w64,
      "i" ∷ i_ptr ↦ i ∗
      "sum" ∷ sum_ptr ↦ sum ∗
      "x" ∷ x_ptr ↦ xv ∗
      "Hsl" ∷ sl ↦* [W64 2, W64 3, W64 4, W64 0, W64 8] ∗
      "%Hi" ∷ ⌜(sint.Z i = 0 ∧ sum = W64 0) ∨ (sint.Z i = 1 ∧ sum = W64 2) ∨
        (sint.Z i = 2 ∧ sum = W64 2) ∨ (sint.Z i = 3 ∧ sum = W64 6)⌝ : IProp GF) $$ [i sum x Hsl]
  · iexists _, _, _
    iframe
    ipureintro; left; exact ⟨rfl, rfl⟩
  wp_for HI
  have hlen5 : sint.Z sl.len = 5 := by simp at Hlen; word
  have hlt : sint.Z i < sint.Z sl.len := by rw [hlen5]; omega
  wp_if_destruct
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, hlt⟩)]
  rcases Hi with ⟨hi, rfl⟩ | ⟨hi, rfl⟩ | ⟨hi, rfl⟩ | ⟨hi, rfl⟩
  · -- x = 2: added, unlabeled `break` of the inner loop
    wp_apply wp_load_slice_index _ _ _ _ (W64 2) (by omega) $$ [Hsl] with Hsl
    · iframe; ipureintro; rw [hi]; rfl
    wp_for
    wp_for_post
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    ipureintro; right; left; exact ⟨by word, rfl⟩
  · -- x = 3: `continue L`
    wp_apply wp_load_slice_index _ _ _ _ (W64 3) (by omega) $$ [Hsl] with Hsl
    · iframe; ipureintro; rw [hi]; rfl
    wp_for
    wp_for_post
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    ipureintro; right; right; left; exact ⟨by word, rfl⟩
  · -- x = 4: added
    wp_apply wp_load_slice_index _ _ _ _ (W64 4) (by omega) $$ [Hsl] with Hsl
    · iframe; ipureintro; rw [hi]; rfl
    wp_for
    wp_for_post
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    ipureintro; right; right; right; exact ⟨by word, rfl⟩
  · -- x = 0: `break L`
    wp_apply wp_load_slice_index _ _ _ _ (W64 0) (by omega) $$ [Hsl] with Hsl
    · iframe; ipureintro; rw [hi]; rfl
    wp_for
    wp_for_post
    wp_for_post
    iapply HΦ
    iexact Hpre
  all_goals (exfalso; omega)

end proof

end Perennial
