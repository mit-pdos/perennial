/-
The proof of `slices.heapSortCmpFunc`.
-/
module

public import Perennial.Spec.slices.heapSortCmpFunc
public import Perennial.Spec.slices.siftDownCmpFunc
public import Perennial.Proof.slices.HeapSortBasics

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

theorem slices.heapSortCmpFunc.wp_proof
    (wp_siftDownCmpFunc : slices.siftDownCmpFunc.spec (GF := GF) (hG := hG)) :
    slices.heapSortCmpFunc.spec (GF := GF) (hG := hG) := by
  intro E _ _ Et _ R _ data a b cmp_code xs
  wp_start as H
  iNamed H
  wp_auto
  have hn : sint.Z (b - a) = sint.Z b - sint.Z a := by word
  have hnn : sint.nat (b - a) = sint.nat b - sint.nat a := by word
  have hi0 : sint.Z (BitVec.sdiv (b - a - W64 1) (W64 2)) = (sint.Z b - sint.Z a - 1) / 2 := by
    rw [sdiv2_nonneg _ (by word)]; word
  -- the outer (heapify) loop
  ihave HI1 : (∃ (i_val : w64) (xs' : List E),
      "i" ∷ i_ptr ↦ i_val ∗
      "Hxs" ∷ data ↦* xs' ∗
      "%Hir" ∷ ⌜-1 ≤ sint.Z i_val ∧ sint.Z i_val ≤ sint.Z b - sint.Z a - 1⌝ ∗
      "%HPerm1" ∷ ⌜xs ≡ₚ xs'⌝ ∗
      "%Heap1" ∷ ⌜IsHeapSeg R xs' (sint.nat a) (sint.nat b) (sint.nat (i_val + W64 1))
        (sint.nat (b - a))⌝ ∗
      "%HSeg1" ∷ ⌜SegSortedFrom R xs' (sint.nat a) (sint.nat b) (sint.nat a + sint.nat (b - a))⌝ ∗
      "%Hout1" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ : IProp GF) $$ [i Hxs]
  · iexists _, xs
    iframe
    ipureintro
    refine ⟨⟨by word, by word⟩, List.Perm.refl _, heap_seg_vacuous R _ _ _ _ _ (by word), ?_,
      outsideSame_refl _ _ _⟩
    intro i j xi xj Hij _ _; omega
  wp_for HI1
  wp_if_destruct
  · -- sift down from `i`
    have e1 : sint.nat (i_val + W64 1) = sint.nat i_val + 1 := by word
    rw [e1] at Heap1
    have hl1 := HPerm1.length_eq
    wp_apply wp_siftDownCmpFunc.1 R data i_val (b - a) a b cmp_code xs' $$ [Hxs]
      with %xs'' ⟨Hxs, %HPermPost, %HSegPost, %HeapPost, %HoutPost⟩
    · iframe Hxs; iframe #; ipureintro
      exact ⟨⟨by word, by word, by word, by word, by word, by word⟩, HSeg1, Heap1⟩
    wp_for_post
    iframe
    iexists (i_val - W64 1), xs''
    iframe
    ipureintro
    have e2 : sint.nat (i_val - W64 1 + W64 1) = sint.nat i_val := by word
    rw [e2]
    exact ⟨⟨by word, by word⟩, HPerm1.trans HPermPost, HeapPost, HSegPost,
      outsideSame_trans _ _ _ _ _ Hout1 HoutPost⟩
  · -- the heap is built
    have e1 : sint.nat (i_val + W64 1) = 0 := by word
    rw [e1] at Heap1
    have hl1 := HPerm1.length_eq
    -- the sorting loop
    ihave HI2 : (∃ (i_val : w64) (xs' : List E),
        "i" ∷ i_ptr ↦ i_val ∗
        "Hxs" ∷ data ↦* xs' ∗
        "%Hir" ∷ ⌜-1 ≤ sint.Z i_val ∧ sint.Z i_val ≤ sint.Z b - sint.Z a - 1⌝ ∗
        "%HPerm2" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Heap2" ∷ ⌜IsHeapSeg R xs' (sint.nat a) (sint.nat b) 0 (sint.nat (i_val + W64 1))⌝ ∗
        "%HSeg2" ∷ ⌜SegSortedFrom R xs' (sint.nat a) (sint.nat b)
          (sint.nat a + sint.nat i_val + 1)⌝ ∗
        "%Hout2" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ : IProp GF) $$ [i Hxs]
    · iexists _, xs'
      iframe
      ipureintro
      have e3 : sint.nat (b - a - W64 1 + W64 1) = sint.nat (b - a) := by word
      have e4 : sint.nat a + sint.nat (b - a - W64 1) + 1 = sint.nat a + sint.nat (b - a) := by word
      rw [e3, e4]
      exact ⟨⟨by word, by word⟩, HPerm1, Heap1, HSeg1, Hout1⟩
    wp_for HI2
    have hl2 := HPerm2.length_eq
    wp_if_destruct
    · ihave %Hlen := ownSlice_len _ _ _ $$ Hxs
      obtain ⟨xi, Hxi⟩ := list_lookup_lt xs' (sint.nat a + sint.nat i_val) (by word)
      obtain ⟨x0, Hx0⟩ := list_lookup_lt xs' (sint.nat a) (by word)
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by constructor <;> word))]
      wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by constructor <;> word))]
      wp_auto
      heap_load_atw Hxi
      heap_load_atw Hx0
      wp_pures
      wp_apply wp_store_slice_index (t := Et) data _ xs' xi $$ [Hxs] with Hxs
      · iframe Hxs; ipureintro; constructor <;> word
      wp_pures
      wp_apply wp_store_slice_index (t := Et) data _ (xs'.set (sint.Z a).toNat xi) x0 $$ [Hxs]
        with Hxs
      · iframe Hxs; ipureintro; refine ⟨by word, ?_⟩; rw [List.length_set]; word
      rw [show (sint.Z (a + i_val)).toNat = sint.nat a + sint.nat i_val by word,
        show (sint.Z a).toNat = sint.nat a from rfl]
      by_cases hz : sint.Z i_val = 0
      · -- `i = 0`: the swap is trivial
        have hz' : i_val = W64 0 := BitVec.toInt_inj.mp (hz.trans (by decide))
        subst hz'
        have e0 : sint.nat (W64 0) = 0 := by decide
        rw [e0, Nat.add_zero] at Hxi
        rw [Hx0] at Hxi; cases Hxi
        rw [e0, Nat.add_zero, list_insert_id (list_lookup_insert_eq _ (by word)), list_insert_id Hx0]
        wp_apply wp_siftDownCmpFunc.2 R data a b cmp_code xs' $$ [Hxs] with Hxs
        · iframe Hxs; iframe #; ipureintro; exact ⟨by word, by word, by word⟩
        wp_for_post
        iframe
        iexists (W64 0 - W64 1), xs'
        iframe
        ipureintro
        have e5 : sint.nat (W64 0 - W64 1 + W64 1) = 0 := by decide
        have e6 : sint.nat (W64 0 - W64 1) = 0 := by decide
        rw [e5, e6]
        rw [e0] at HSeg2
        exact ⟨⟨by word, by word⟩, HPerm2, heap_seg_vacuous R _ _ _ _ _ (by omega), HSeg2, Hout2⟩
      · -- `i ≥ 1`: sift the new root down in `[0, i)`
        have e1 : sint.nat (i_val + W64 1) = sint.nat i_val + 1 := by word
        rw [e1] at Heap2
        wp_apply wp_siftDownCmpFunc.1 R data (W64 0) i_val a b cmp_code
          ((xs'.set (sint.nat a) xi).set (sint.nat a + sint.nat i_val) x0) $$ [Hxs]
          with %xs3 ⟨Hxs, %HP, %HS, %HH, %HO⟩
        · iframe Hxs; iframe #; ipureintro
          refine ⟨⟨by word, by word, by word, by word, by rw [List.length_set, List.length_set]; word,
            by rw [List.length_set, List.length_set]; word⟩, ?_, ?_⟩
          · exact heap_pop_seg R xs' _ _ _ x0 xi Heap2 Hx0 Hxi (by word) (by word) HSeg2
          · rw [show sint.nat (W64 0) + 1 = 1 from rfl]
            exact heap_pop_heap R xs' _ _ _ x0 xi (by word) Heap2
        wp_for_post
        iframe
        iexists (i_val - W64 1), xs3
        iframe
        ipureintro
        have e2 : sint.nat (i_val - W64 1 + W64 1) = sint.nat i_val := by word
        have e3 : sint.nat a + sint.nat (i_val - W64 1) + 1 = sint.nat a + sint.nat i_val := by word
        rw [e2, e3]
        refine ⟨⟨by word, by word⟩,
          HPerm2.trans ((swap_perm xs' _ _ xi x0 Hxi Hx0).trans HP), HH, HS, ?_⟩
        exact outsideSame_trans _ _ _ _ _ Hout2 (outsideSame_trans _ _ _ _ _
          (outsideSame_swap xs' _ _ xi x0 _ _ ⟨by omega, by word⟩ ⟨by omega, by word⟩) HO)
    · -- done
      iapply HΦ
      iframe
      ipureintro
      have e0 : sint.nat i_val = 0 := by word
      rw [e0] at HSeg2
      refine ⟨HPerm2, ?_, Hout2⟩
      intro i j xi xj Hij hxi hxj
      exact HSeg2 i j xi xj ⟨Hij.1.2, by omega, ⟨by omega, Hij.2⟩, ⟨Hij.1.1, by omega⟩⟩ hxi hxj

end proof

end Perennial
