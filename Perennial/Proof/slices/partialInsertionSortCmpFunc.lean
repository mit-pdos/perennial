/-
The proof of `slices.partialInsertionSortCmpFunc`.
-/
module

public import Perennial.Spec.slices.partialInsertionSortCmpFunc
public import Perennial.Proof.slices.InsertionSortBasics

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

theorem slices.partialInsertionSortCmpFunc.wp_proof : slices.partialInsertionSortCmpFunc.spec (GF := GF) (hG := hG) := by
  intro E _ _ Et _ R _ data a b cmp_code xs
  wp_start as H
  iNamed H
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hxs
  ihave HI : (∃ (jc i_val : w64) (xs' : List E),
      "jc" ∷ j_ptr ↦ jc ∗
      "i" ∷ i_ptr ↦ i_val ∗
      "Hxs" ∷ data ↦* xs' ∗
      "%irange" ∷ ⌜sint.Z a + 1 ≤ sint.Z i_val ∧ sint.Z i_val ≤ sint.Z b⌝ ∗
      "%HPerm1" ∷ ⌜xs ≡ₚ xs'⌝ ∗
      "%Hsorted" ∷ ⌜IsSortedSeg R xs' (sint.nat a) (sint.nat i_val)⌝ ∗
      "%Houtside1" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ : IProp GF) $$ [j i Hxs]
  · iexists _, _, xs
    iframe
    ipureintro
    have : sint.nat (a + W64 1) = sint.nat a + 1 := by word
    rw [this]
    exact ⟨⟨by word, by word⟩, List.Perm.refl _, isSortedSeg_one R xs _, outsideSame_refl _ _ _⟩
  wp_for HI
  by_cases Hjc : sint.Z jc < sint.Z (W64 5)
  case neg =>
    simp only [Hjc, decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    exact ⟨HPerm1, trivial, Houtside1⟩
  simp only [Hjc, _root_.decide_true, ↓reduceIte]
  wp_auto
  ihave HS : (∃ (i_val : w64) (xs' : List E),
      "i" ∷ i_ptr ↦ i_val ∗
      "Hxs" ∷ data ↦* xs' ∗
      "%irange" ∷ ⌜sint.Z a + 1 ≤ sint.Z i_val ∧ sint.Z i_val ≤ sint.Z b⌝ ∗
      "%HPerm1" ∷ ⌜xs ≡ₚ xs'⌝ ∗
      "%Hsorted" ∷ ⌜IsSortedSeg R xs' (sint.nat a) (sint.nat i_val)⌝ ∗
      "%Houtside1" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ : IProp GF) $$ [i Hxs]
  · iexists _, _
    iframe
    ipureintro
    exact ⟨irange, HPerm1, Hsorted, Houtside1⟩
  clear irange HPerm1 Hsorted Houtside1 i_val xs'
  wp_for HS
  have hlen' := HPerm1.length_eq
  wp_if_destruct
  · list_elem xs' (sint.nat i_val) as x0
    list_elem xs' (sint.nat (i_val - W64 1)) as x1
    slice_index_if
    wp_apply wp_load_slice_index data (sint.Z i_val) xs' _ x0 (by omega) $$ [Hxs] with Hxs
    · iframe Hxs; ipureintro; exact Hx0_lookup
    slice_index_if
    wp_apply wp_load_slice_index data (sint.Z (i_val - W64 1)) xs' _ x1 (by word) $$ [Hxs]
      with Hxs
    · iframe Hxs; ipureintro; exact Hx1_lookup
    wp_apply ins_wp_cmp R cmp_code $$ Hcmp with %r %Hr
    have hi1 : sint.nat (i_val - W64 1) = sint.nat i_val - 1 := by word
    rw [hi1] at Hx1_lookup
    by_cases hc : sint.Z r < sint.Z (W64 0)
    case neg =>
      -- keep scanning
      simp only [hc, decide_false, Bool.not_false]
      cleanup_bool_decide
      wp_auto
      wp_for_post
      iframe
      iexists (i_val + W64 1), xs'
      iframe
      ipureintro
      have hi2 : sint.nat (i_val + W64 1) = sint.nat i_val + 1 := by word
      rw [hi2]
      exact ⟨⟨by word, by word⟩, HPerm1,
        isSortedSeg_scan R _ _ _ _ _ Hsorted (by word) Hx0_lookup Hx1_lookup
          (fun h => hc (Hr.2 h)), Houtside1⟩
    simp only [hc, _root_.decide_true, Bool.not_true]
    cleanup_bool_decide
    wp_auto
    wp_if_destruct
    · subst Hif; omega
    wp_if_destruct
    · -- short slice: give up
      wp_for_post
      iapply HΦ
      iframe
      ipureintro
      exact ⟨HPerm1, trivial, Houtside1⟩
    -- swap `data[i-1]` and `data[i]`
    have hidx : (sint.Z (i_val - W64 1)).toNat = sint.nat i_val - 1 := hi1
    have hidx' : (sint.Z i_val).toNat = sint.nat i_val := rfl
    slice_index_if
    wp_auto
    slice_index_if
    wp_auto
    slice_index_if
    wp_apply wp_load_slice_index data (sint.Z (i_val - W64 1)) xs' _ x1 (by word) $$ [Hxs] with Hxs
    · iframe Hxs; ipureintro; rw [hidx]; exact Hx1_lookup
    slice_index_if
    wp_apply wp_load_slice_index data (sint.Z i_val) xs' _ x0 (by word) $$ [Hxs] with Hxs
    · iframe Hxs; ipureintro; exact Hx0_lookup
    wp_pures
    wp_apply wp_store_slice_index data (sint.Z i_val) xs' x1 $$ [Hxs] with Hxs
    · iframe Hxs; ipureintro; word
    wp_pures
    wp_apply wp_store_slice_index data (sint.Z (i_val - W64 1)) _ x0 $$ [Hxs] with Hxs
    · iframe Hxs; ipureintro; simp only [List.length_set]; word
    rw [hidx, hidx']
    have Hperm2 : xs ≡ₚ (xs'.set (sint.nat i_val) x1).set (sint.nat i_val - 1) x0 :=
      HPerm1.trans (swap_perm _ _ _ _ _ Hx1_lookup Hx0_lookup)
    have Houtside2 : OutsideSame xs ((xs'.set (sint.nat i_val) x1).set (sint.nat i_val - 1) x0)
        (sint.nat a) (sint.nat b) :=
      outsideSame_trans _ _ _ _ _ Houtside1
        (outsideSame_swap _ _ _ _ _ _ _ ⟨by word, by word⟩ ⟨by word, by word⟩)
    have Hsorted2 : IsSortedSeg R ((xs'.set (sint.nat i_val) x1).set (sint.nat i_val - 1) x0)
        (sint.nat a) (sint.nat i_val - 1) :=
      isSortedSeg_swap_hi R _ _ _ _ _ _ _
        (isSortedSeg_mono R _ _ _ _ (by omega) Hsorted) (by omega) (by omega)
    have hlen2 := Hperm2.length_eq
    generalize (xs'.set (sint.nat i_val) x1).set (sint.nat i_val - 1) x0 = xs2
      at Hperm2 Houtside2 Hsorted2 hlen2 ⊢
    have Header2 := header_preserve R xs xs2 _ _ Header Hperm2 Houtside2 (by word)
    clear Hx0_lookup Hx1_lookup Hr hc x0 x1 Hsorted Houtside1 HPerm1 xs' hlen'
    -- join point after shifting the smaller element to the left
    wp_bind (If _ _ _)
    iapply wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ xs3,
        "Hxs" ∷ data ↦* xs3 ∗ "i" ∷ i_ptr ↦ i_val ∗ "a" ∷ a_ptr ↦ a ∗
        "data" ∷ data_ptr ↦ data ∗ "cmp" ∷ cmp_ptr ↦ cmp_code ∗
        "%Hperm3" ∷ ⌜xs ≡ₚ xs3⌝ ∗
        "%Hsorted3" ∷ ⌜IsSortedSeg R xs3 (sint.nat a) (sint.nat i_val)⌝ ∗
        "%Houtside3" ∷ ⌜OutsideSame xs xs3 (sint.nat a) (sint.nat b)⌝)) $$ [Hxs i a data cmp]
    · wp_if_destruct
      · ihave HL : (∃ (jl : w64) (xs3 : List E),
            "jl" ∷ j_ptr ↦ jl ∗
            "Hxs" ∷ data ↦* xs3 ∗
            "%jrange" ∷ ⌜sint.Z a ≤ sint.Z jl ∧ sint.Z jl ≤ sint.Z i_val - 1⌝ ∗
            "%Hperm3" ∷ ⌜xs ≡ₚ xs3⌝ ∗
            "%HsortedBr" ∷ ⌜InsBr R xs3 (sint.nat a) (sint.nat i_val - 1) (sint.nat jl)⌝ ∗
            "%Houtside3" ∷ ⌜OutsideSame xs xs3 (sint.nat a) (sint.nat b)⌝ : IProp GF) $$ [j Hxs]
        · iexists _, xs2
          iframe
          ipureintro
          rw [hi1]
          exact ⟨⟨by word, by word⟩, Hperm2, insBr_init R _ _ _ Hsorted2, Houtside2⟩
        clear Hperm2 Houtside2 Hsorted2 hlen2
        iapply (ins_wp_shift_left R data a b i_val cmp_code xs cmp_ptr a_ptr data_ptr i_ptr j_ptr
          Header Hab_bound Hlen irange (by assumption)) $$ Hcmp cmp a data i HL
      · isplitl []
        · itrivial
        iexists xs2
        iframe
        ipureintro
        have : sint.nat i_val = sint.nat a + 1 := by word
        rw [this]
        exact ⟨Hperm2, isSortedSeg_one R _ _, Houtside2⟩
    clear Hperm2 Houtside2 Hsorted2 hlen2 Header2
    iintro %v ⟨%Hv, HQ⟩
    subst Hv
    icases HQ with ⟨%xs3, HQ⟩
    iNamed HQ
    wp_auto
    wp_if_destruct
    · ihave HRt : (∃ (jr : w64) (xs4 : List E),
          "jr" ∷ j_ptr ↦ jr ∗
          "Hxs" ∷ data ↦* xs4 ∗
          "%jrange" ∷ ⌜sint.Z i_val < sint.Z jr ∧ sint.Z jr ≤ sint.Z b⌝ ∗
          "%Hperm4" ∷ ⌜xs ≡ₚ xs4⌝ ∗
          "%Hsorted4" ∷ ⌜IsSortedSeg R xs4 (sint.nat a) (sint.nat i_val)⌝ ∗
          "%Houtside4" ∷ ⌜OutsideSame xs xs4 (sint.nat a) (sint.nat b)⌝ : IProp GF) $$ [j Hxs]
      · iexists _, xs3
        iframe
        ipureintro
        exact ⟨⟨by word, by word⟩, Hperm3, Hsorted3, Houtside3⟩
      clear Hperm3 Hsorted3 Houtside3
      iapply (ins_wp_shift_right R data a b i_val cmp_code xs cmp_ptr b_ptr data_ptr j_ptr _
        Hab_bound Hlen irange) $$ Hcmp cmp b data HRt
      iintro %xs4 ⟨Hxs, cmp, b, data, %Hpost⟩
      wp_for_post
      iframe
      iexists (jc + W64 1), i_val, xs4
      iframe
      ipureintro
      exact ⟨irange, Hpost⟩
    · wp_for_post
      iframe
      iexists (jc + W64 1), i_val, xs3
      iframe
      ipureintro
      exact ⟨irange, Hperm3, Hsorted3, Houtside3⟩
  · -- `i = b`: return true
    have hib : i_val = b := by word
    subst hib
    rw [decide_eq_true rfl]
    wp_auto
    wp_for_post
    iapply HΦ
    iframe
    ipureintro
    exact ⟨HPerm1, Hsorted, Houtside1⟩

end proof

end Perennial
