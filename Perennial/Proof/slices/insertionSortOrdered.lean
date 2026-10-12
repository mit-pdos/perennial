/-
The proof of `slices.insertionSortOrdered`.
-/
module

public import Perennial.Spec.slices.insertionSortOrdered
public import Perennial.Proof.slices.OrderedInsertionSortBasics

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

theorem slices.insertionSortOrdered.wp_proof : slices.insertionSortOrdered.spec (GF := GF) (hG := hG) := by
  intro E _ _ Et _ R _ data a b xs
  wp_start as H
  iNamed H
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hxs
  ihave HI1 : (∃ (i_val : w64) (xs' : List E),
      "i" ∷ i_ptr ↦ i_val ∗
      "Hxs" ∷ data ↦* xs' ∗
      "%irange" ∷ ⌜sint.Z a + 1 ≤ sint.Z i_val ∧ sint.Z i_val ≤ max (sint.Z a + 1) (sint.Z b)⌝ ∗
      "%HPerm1" ∷ ⌜xs ≡ₚ xs'⌝ ∗
      "%Hsorted" ∷ ⌜IsSortedSeg R xs' (sint.nat a) (sint.nat i_val)⌝ ∗
      "%Houtside1" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ : IProp GF) $$ [i Hxs]
  · iexists _, xs
    iframe
    ipureintro
    have : sint.Z (a + W64 1) = sint.Z a + 1 := by word
    refine ⟨⟨by omega, by omega⟩, List.Perm.refl _, ?_, outsideSame_refl _ _ _⟩
    rw [show sint.nat (a + W64 1) = sint.nat a + 1 by word]
    exact isSortedSeg_one R xs _
  wp_for HI1
  by_cases Hif : sint.Z i_val < sint.Z b
  · simp only [Hif, _root_.decide_true, ↓reduceIte]
    wp_auto
    have hlen' := HPerm1.length_eq
    ihave HI2 : (∃ (j_val : w64) (xs'' : List E),
        "j" ∷ j_ptr ↦ j_val ∗
        "Hxs" ∷ data ↦* xs'' ∗
        "%jrange" ∷ ⌜sint.Z a ≤ sint.Z j_val ∧ sint.Z j_val ≤ sint.Z i_val⌝ ∗
        "%Hperm2" ∷ ⌜xs ≡ₚ xs''⌝ ∗
        "%HsortedBr" ∷ ⌜InsBr R xs'' (sint.nat a) (sint.nat i_val) (sint.nat j_val)⌝ ∗
        "%Houtside2" ∷ ⌜OutsideSame xs xs'' (sint.nat a) (sint.nat b)⌝ : IProp GF) $$ [j Hxs]
    · iexists _, xs'
      iframe
      ipureintro
      exact ⟨⟨by omega, by omega⟩, HPerm1, insBr_init R _ _ _ Hsorted, Houtside1⟩
    iapply (ord_wp_insertion_inner (Et := Et) R data a b i_val xs a_ptr data_ptr j_ptr _
      Hab_bound Hlen irange Hif) $$ Hless a data HI2
    iintro %xs'' ⟨Hxs, a, data, %Hpost⟩
    wp_for_post
    iframe
    iexists (i_val + W64 1), xs''
    iframe
    ipureintro
    have hi1 : sint.nat (i_val + W64 1) = sint.nat i_val + 1 := by word
    rw [hi1]
    exact ⟨⟨by word, by word⟩, Hpost⟩
  · simp only [Hif, decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    exact ⟨HPerm1, isSortedSeg_mono R _ _ _ _ (by word) Hsorted, Houtside1⟩

end proof

end Perennial
