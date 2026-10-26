/-
The proof of `slices.reverseRangeOrdered`.
-/
module

public import Perennial.Spec.slices.reverseRangeOrdered
public import Perennial.Proof.slices.OrderedPdqSortBasics

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

theorem slices.reverseRangeOrdered.wp_proof : slices.reverseRangeOrdered.spec (GF := GF) (hG := hG) := by
  intro E _ _ Et _ data a b xs
  wp_start as H
  iNamed H
  wp_auto
  ihave HI : (∃ (xs1 : List E) (i_val j_val : w64),
      "Hxs" ∷ data ↦* xs1 ∗
      "i" ∷ i_ptr ↦ i_val ∗
      "j" ∷ j_ptr ↦ j_val ∗
      "%ij_bound" ∷ ⌜sint.Z a ≤ sint.Z i_val ∧ sint.Z j_val < sint.Z b⌝ ∗
      "%HPerm1" ∷ ⌜xs ≡ₚ xs1⌝ ∗
      "%Houtside1" ∷ ⌜OutsideSame xs xs1 (sint.nat a) (sint.nat b)⌝ : IProp GF) $$ [Hxs i j]
  · iexists xs, _, _
    iframe
    ipureintro
    exact ⟨by word, List.Perm.refl _, outsideSame_refl _ _ _⟩
  wp_for HI
  wp_if_destruct
  · have Hl := HPerm1.length_eq
    ihave %Hlen := ownSlice_len _ _ _ $$ Hxs
    list_elem xs1 (sint.nat j_val) as xj
    list_elem xs1 (sint.nat i_val) as xi
    slice_index_if
    wp_auto
    slice_index_if
    wp_auto
    slice_index_if
    wp_apply wp_load_slice_index data (sint.Z j_val) xs1 _ xj (by word) $$ [Hxs] with Hxs
    · iframe Hxs; ipureintro; exact Hxj_lookup
    slice_index_if
    wp_apply wp_load_slice_index data (sint.Z i_val) xs1 _ xi (by word) $$ [Hxs] with Hxs
    · iframe Hxs; ipureintro; exact Hxi_lookup
    wp_pures
    wp_apply wp_store_slice_index data (sint.Z i_val) xs1 xj $$ [Hxs] with Hxs
    · iframe Hxs; ipureintro; constructor <;> word
    wp_pures
    wp_apply wp_store_slice_index data (sint.Z j_val) _ xi $$ [Hxs] with Hxs
    · iframe Hxs; ipureintro; simp only [List.length_set]; constructor <;> word
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    ipureintro
    refine ⟨by word, ?_, ?_⟩
    · exact HPerm1.trans (swap_perm xs1 (sint.nat j_val) (sint.nat i_val) xj xi
        Hxj_lookup Hxi_lookup)
    · exact outsideSame_trans _ _ _ _ _ Houtside1
        (outsideSame_swap _ _ _ _ _ _ _ ⟨by word, by word⟩ ⟨by word, by word⟩)
  · iapply HΦ
    iframe
    ipureintro
    exact ⟨HPerm1, Houtside1⟩

end proof

end Perennial
