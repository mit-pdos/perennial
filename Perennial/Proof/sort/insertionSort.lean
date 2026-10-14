/-
The proof of `sort.insertionSort` over a `sort.Interface`: the proof of `slices.insertionSortCmpFunc`
(`Perennial/Proof/slices/insertionSortCmpFunc.lean`) with `Less`/`Swap` calls.
-/
module

public import Perennial.Spec.sort.insertionSort
public import Perennial.Proof.sort.SorterBasics
public import Perennial.Proof.slices.InsertionSortBasics

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open slices

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

theorem sort.insertionSort.wp_proof : sort.insertionSort.spec (GF := GF) (hG := hG) := fun {E} x own R _ a b xs => by
  -- (`fun`, not `intro`: `wp_apply_post` runs `whnfR` outside the goal's context, so a
  -- `wp_apply` fails silently on binders introduced by a tactic)
  wp_start as H
  iNamed H
  wp_auto
  ihave HI1 : (∃ (i_val : w64) (xs' : List E),
      "i" ∷ i_ptr ↦ i_val ∗
      "Hxs" ∷ own xs' ∗
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
        "Hxs" ∷ own xs'' ∗
        "%jrange" ∷ ⌜sint.Z a ≤ sint.Z j_val ∧ sint.Z j_val ≤ sint.Z i_val⌝ ∗
        "%Hperm2" ∷ ⌜xs ≡ₚ xs''⌝ ∗
        "%HsortedBr" ∷ ⌜InsBr R xs'' (sint.nat a) (sint.nat i_val) (sint.nat j_val)⌝ ∗
        "%Houtside2" ∷ ⌜OutsideSame xs xs'' (sint.nat a) (sint.nat b)⌝ : IProp GF) $$ [j Hxs]
    · iexists _, xs'
      iframe
      ipureintro
      exact ⟨⟨by omega, by omega⟩, HPerm1, insBr_init R _ _ _ Hsorted, Houtside1⟩
    wp_for HI2
    have hlen'' := Hperm2.length_eq
    wp_if_destruct
    · list_elem xs'' (sint.nat j_val) as x0
      list_elem xs'' (sint.nat (j_val - W64 1)) as x1
      wp_apply wp_sorter_Less x own R xs'' j_val (j_val - W64 1) x0 x1 (by word) (by word)
        Hx0_lookup Hx1_lookup $$ [$Hsrt $Hxs] as %r ⟨Hxs, %Hr⟩
      have hj1 : sint.nat (j_val - W64 1) = sint.nat j_val - 1 := by word
      cases r
      · bool_if
        rw [hj1] at Hx1_lookup
        have hR : ¬ R x0 x1 := fun h => by simpa using Hr.2 h
        have Hs := insBr_done_cmp R _ _ _ _ _ _ HsortedBr (by word) (by word) Hx0_lookup Hx1_lookup hR
        wp_for_post
        iframe
        iexists (i_val + W64 1), xs''
        iframe
        ipureintro
        have hi1 : sint.nat (i_val + W64 1) = sint.nat i_val + 1 := by word
        rw [hi1]
        exact ⟨⟨by word, by word⟩, Hperm2, Hs, Houtside2⟩
      · bool_if
        wp_auto
        wp_apply wp_sorter_Swap x own R xs'' j_val (j_val - W64 1) x0 x1 (by word) (by word)
          Hx0_lookup Hx1_lookup $$ [$Hsrt $Hxs] as Hxs
        wp_for_post
        iframe
        iexists (j_val - W64 1), _
        iframe
        ipureintro
        rw [hj1] at Hx1_lookup ⊢
        have hR := Hr.1 rfl
        refine ⟨⟨by word, by word⟩, ?_, ?_, ?_⟩
        · exact Hperm2.trans (swap_perm _ _ _ _ _ Hx0_lookup Hx1_lookup)
        · rw [← swap_set_comm _ _ _ _ _ Hx0_lookup Hx1_lookup]
          exact insBr_swap R _ _ _ _ _ _ HsortedBr (by word) (by word) Hx0_lookup Hx1_lookup hR
        · exact outsideSame_trans _ _ _ _ _ Houtside2
            (outsideSame_swap _ _ _ _ _ _ _ ⟨by word, by word⟩ ⟨by word, by word⟩)
    · have Hs := insBr_done_a R _ _ _ _ HsortedBr (by word)
      wp_for_post
      iframe
      iexists (i_val + W64 1), xs''
      iframe
      ipureintro
      have hi1 : sint.nat (i_val + W64 1) = sint.nat i_val + 1 := by word
      rw [hi1]
      exact ⟨⟨by word, by word⟩, Hperm2, Hs, Houtside2⟩
  · simp only [Hif, decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    exact ⟨HPerm1, isSortedSeg_mono R _ _ _ _ (by word) Hsorted, Houtside1⟩

end proof

end Perennial
