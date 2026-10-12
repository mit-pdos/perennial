/-
The proof of `sort.partialInsertionSort` over a `sort.Interface`: the proof of `slices.partialInsertionSortCmpFunc`
(`Perennial/Proof/slices/partialInsertionSortCmpFunc.lean`) with `Less`/`Swap` calls.
-/
module

public import Perennial.Spec.sort.partialInsertionSort
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

theorem sort.partialInsertionSort.wp_proof : sort.partialInsertionSort.spec (GF := GF) (hG := hG) := fun {E} x own R _ a b xs => by
  -- (`fun`, not `intro`: `wp_apply_post` runs `whnfR` outside the goal's context, so a
  -- `wp_apply` fails silently on binders introduced by a tactic)
  wp_start as H
  iNamed H
  wp_auto
  ihave HI : (∃ (jc i_val : w64) (xs' : List E),
      "jc" ∷ j_ptr ↦ jc ∗
      "i" ∷ i_ptr ↦ i_val ∗
      "Hxs" ∷ own xs' ∗
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
      "Hxs" ∷ own xs' ∗
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
    wp_apply wp_sorter_Less x own R xs' i_val (i_val - W64 1) x0 x1 (by word) (by word)
      Hx0_lookup Hx1_lookup $$ [$Hsrt $Hxs] as %r ⟨Hxs, %Hr⟩
    have hi1 : sint.nat (i_val - W64 1) = sint.nat i_val - 1 := by word
    have hidx : (sint.Z (i_val - W64 1)).toNat = sint.nat i_val - 1 := hi1
    cases r
    case false =>
      -- keep scanning
      simp only [Bool.not_false]
      (try bool_if)
      wp_auto
      wp_for_post
      iframe
      iexists (i_val + W64 1), xs'
      iframe
      ipureintro
      rw [hi1] at Hx1_lookup
      have hi2 : sint.nat (i_val + W64 1) = sint.nat i_val + 1 := by word
      rw [hi2]
      exact ⟨⟨by word, by word⟩, HPerm1,
        isSortedSeg_scan R _ _ _ _ _ Hsorted (by word) Hx0_lookup Hx1_lookup
          (fun h => by simpa using Hr.2 h), Houtside1⟩
    simp only [Bool.not_true]
    (try bool_if)
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
    -- swap `data[i]` and `data[i-1]`
    wp_apply wp_sorter_Swap x own R xs' i_val (i_val - W64 1) x0 x1 (by word) (by word)
      Hx0_lookup Hx1_lookup $$ [$Hsrt $Hxs] as Hxs
    rw [hi1] at Hx1_lookup ⊢
    rw [← swap_set_comm _ _ _ _ _ Hx0_lookup Hx1_lookup]
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
    clear Hx0_lookup Hx1_lookup Hr x0 x1 Hsorted Houtside1 HPerm1 xs' hlen'
    -- join point after shifting the smaller element to the left
    wp_bind (If _ _ _)
    iapply wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ xs3,
        "Hxs" ∷ own xs3 ∗ "i" ∷ i_ptr ↦ i_val ∗ "a" ∷ a_ptr ↦ a ∗
        "data" ∷ data_ptr ↦ (interface.ok x : GoInterface) ∗
        "%Hperm3" ∷ ⌜xs ≡ₚ xs3⌝ ∗
        "%Hsorted3" ∷ ⌜IsSortedSeg R xs3 (sint.nat a) (sint.nat i_val)⌝ ∗
        "%Houtside3" ∷ ⌜OutsideSame xs xs3 (sint.nat a) (sint.nat b)⌝)) $$ [Hxs i a data]
    · wp_if_destruct
      · ihave HL : (∃ (jl : w64) (xs3 : List E),
            "jl" ∷ j_ptr ↦ jl ∗
            "Hxs" ∷ own xs3 ∗
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
        wp_for HL
        have Header2' := header_preserve R xs xs3 _ _ Header Hperm3 Houtside3 (by word)
        have hlen3 := Hperm3.length_eq
        have hsi : sint.nat i_val - 1 + 1 = sint.nat i_val := by word
        by_cases Hjl : sint.Z (W64 1) ≤ sint.Z jl
        case neg =>
          simp only [Hjl, decide_false, Bool.false_eq_true, ↓reduceIte]
          isplitl []
          · itrivial
          iexists xs3
          iframe
          ipureintro
          refine ⟨Hperm3, ?_, Houtside3⟩
          rw [← hsi]
          exact insBr_done_a R _ _ _ _ HsortedBr (by word)
        simp only [Hjl, _root_.decide_true, ↓reduceIte]
        wp_auto
        list_elem xs3 (sint.nat jl) as y0
        list_elem xs3 (sint.nat (jl - W64 1)) as y1
        have hj1 : sint.nat (jl - W64 1) = sint.nat jl - 1 := by word
        wp_apply wp_sorter_Less x own R xs3 jl (jl - W64 1) y0 y1 (by word) (by word)
          Hy0_lookup Hy1_lookup $$ [$Hsrt $Hxs] as %r' ⟨Hxs, %Hr'⟩
        rw [hj1] at Hy1_lookup
        cases r'
        case false =>
          -- break
          simp only [Bool.not_false]
          (try bool_if)
          wp_auto
          wp_for_post
          isplitl []
          · itrivial
          iexists xs3
          iframe
          ipureintro
          refine ⟨Hperm3, ?_, Houtside3⟩
          rw [← hsi]
          by_cases hja : sint.nat jl = sint.nat a
          · exact insBr_done_a R _ _ _ _ HsortedBr hja
          · exact insBr_done_cmp R _ _ _ _ _ _ HsortedBr (by word) (by word) Hy0_lookup Hy1_lookup
              (fun h => by simpa using Hr'.2 h)
        simp only [Bool.not_true]
        (try bool_if)
        wp_auto
        have hRy := Hr'.1 rfl
        have hja : sint.nat a < sint.nat jl := by
          by_cases hja : sint.nat jl = sint.nat a
          · exfalso
            rw [hja] at Hy0_lookup Hy1_lookup
            exact header_contra R _ _ _ _ _ Header2' (by word) (by word) Hy0_lookup Hy1_lookup hRy
          · word
        rw [← hj1] at Hy1_lookup
        wp_apply wp_sorter_Swap x own R xs3 jl (jl - W64 1) y0 y1 (by word) (by word)
          Hy0_lookup Hy1_lookup $$ [$Hsrt $Hxs] as Hxs
        rw [hj1] at Hy1_lookup ⊢
        wp_for_post
        iframe
        iexists (jl - W64 1), _
        iframe
        ipureintro
        rw [hj1]
        refine ⟨⟨by word, by word⟩, ?_, ?_, ?_⟩
        · exact Hperm3.trans (swap_perm _ _ _ _ _ Hy0_lookup Hy1_lookup)
        · rw [← swap_set_comm _ _ _ _ _ Hy0_lookup Hy1_lookup]
          exact insBr_swap R _ _ _ _ _ _ HsortedBr hja (by word) Hy0_lookup Hy1_lookup hRy
        · exact outsideSame_trans _ _ _ _ _ Houtside3
            (outsideSame_swap _ _ _ _ _ _ _ ⟨by word, by word⟩ ⟨by word, by word⟩)
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
          "Hxs" ∷ own xs4 ∗
          "%jrange" ∷ ⌜sint.Z i_val < sint.Z jr ∧ sint.Z jr ≤ sint.Z b⌝ ∗
          "%Hperm4" ∷ ⌜xs ≡ₚ xs4⌝ ∗
          "%Hsorted4" ∷ ⌜IsSortedSeg R xs4 (sint.nat a) (sint.nat i_val)⌝ ∗
          "%Houtside4" ∷ ⌜OutsideSame xs xs4 (sint.nat a) (sint.nat b)⌝ : IProp GF) $$ [j Hxs]
      · iexists _, xs3
        iframe
        ipureintro
        exact ⟨⟨by word, by word⟩, Hperm3, Hsorted3, Houtside3⟩
      clear Hperm3 Hsorted3 Houtside3
      wp_for HRt
      have hlen4 := Hperm4.length_eq
      wp_if_destruct
      · list_elem xs4 (sint.nat jr) as y0
        list_elem xs4 (sint.nat (jr - W64 1)) as y1
        have hj1 : sint.nat (jr - W64 1) = sint.nat jr - 1 := by word
        wp_apply wp_sorter_Less x own R xs4 jr (jr - W64 1) y0 y1 (by word) (by word)
          Hy0_lookup Hy1_lookup $$ [$Hsrt $Hxs] as %r' ⟨Hxs, %Hr'⟩
        cases r'
        case false =>
          -- break
          simp only [Bool.not_false]
          (try bool_if)
          wp_auto
          wp_for_post
          wp_for_post
          iframe
          iexists (jc + W64 1), i_val, xs4
          iframe
          ipureintro
          exact ⟨irange, Hperm4, Hsorted4, Houtside4⟩
        simp only [Bool.not_true]
        (try bool_if)
        wp_auto
        wp_apply wp_sorter_Swap x own R xs4 jr (jr - W64 1) y0 y1 (by word) (by word)
          Hy0_lookup Hy1_lookup $$ [$Hsrt $Hxs] as Hxs
        rw [hj1] at Hy1_lookup ⊢
        wp_for_post
        iframe
        iexists (jr + W64 1), _
        iframe
        ipureintro
        refine ⟨⟨by word, by word⟩, ?_, ?_, ?_⟩
        · exact Hperm4.trans (swap_perm _ _ _ _ _ Hy0_lookup Hy1_lookup)
        · rw [← swap_set_comm _ _ _ _ _ Hy0_lookup Hy1_lookup]
          exact isSortedSeg_swap_hi R _ _ _ _ _ _ _ Hsorted4 (by word) (by word)
        · exact outsideSame_trans _ _ _ _ _ Houtside4
            (outsideSame_swap _ _ _ _ _ _ _ ⟨by word, by word⟩ ⟨by word, by word⟩)
      · wp_for_post
        iframe
        iexists (jc + W64 1), i_val, xs4
        iframe
        ipureintro
        exact ⟨irange, Hperm4, Hsorted4, Houtside4⟩
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
