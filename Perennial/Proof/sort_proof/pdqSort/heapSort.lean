/-
Specs of `siftDown` and `heapSort` over a `sort.Interface`
(`slices_proof/pdqSort/heapSort.lean` with `Less`/`Swap` calls).
-/
module

public import Perennial.Proof.sort_proof.pdqSort.sort_basics
public import Perennial.Proof.slices.HeapSortBasics

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace sort

open slices

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]
variable {E : Type} (x : GoInterfaceOk) (own : List E → IProp GF)
variable (R : E → E → Prop) [StrictWeakOrder R]

set_option maxHeartbeats 1000000 in
theorem wp_siftDown (lo hi a b : w64) (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        "Hxs" ∷ own xs ∗
        "#Hsrt" ∷ isSorter x own R ∗
        "%H_bounds" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a ≤ sint.Z a + sint.Z lo ∧
                        sint.Z a + sint.Z lo < sint.Z a + sint.Z hi ∧
                        sint.Z a + sint.Z hi ≤ sint.Z b ∧
                        sint.Z b ≤ xs.length ∧
                        xs.length ≤ 2 ^ 62⌝ ∗
        "%HSegSorted" ∷ ⌜∀ (i j : Nat) (xi xj : E), i < j ∧ sint.nat a + sint.nat hi ≤ j ∧
                    (sint.nat a ≤ j ∧ j < sint.nat b) ∧
                    (sint.nat a ≤ i ∧ i < sint.nat b) →
                    xs[i]? = some xi →
                    xs[j]? = some xj → ¬ R xj xi⌝ ∗
        "%Heap" ∷ ⌜IsHeapSeg R xs (sint.nat a) (sint.nat b) (sint.nat lo + 1) (sint.nat hi)⌝ }}
      (App (App (App (App (Val (@! siftDown)) (Val #(interface.ok x))) (Val #lo)) (Val #hi)) (Val #a))
    {{ (xs' : List E), RET #();
        "Hxs" ∷ own xs' ∗
        "%HPermPost" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%HSegSortedPost" ∷ ⌜∀ (i j : Nat) (xi xj : E), i < j ∧ sint.nat a + sint.nat hi ≤ j ∧
                    (sint.nat a ≤ j ∧ j < sint.nat b) ∧
                    (sint.nat a ≤ i ∧ i < sint.nat b) →
                    xs'[i]? = some xi →
                    xs'[j]? = some xj → ¬ R xj xi⌝ ∗
        "%Heap" ∷ ⌜IsHeapSeg R xs' (sint.nat a) (sint.nat b) (sint.nat lo) (sint.nat hi)⌝ ∗
        "%Houtside" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ }} := by
  wp_start as H
  iNamed H
  wp_auto
  have Hinit := sift_inv_init R xs (sint.nat a) (sint.nat b) (sint.nat lo) (sint.nat hi) Heap
  ihave HI : (∃ (root_val : w64) (xs' : List E),
      "root" ∷ root_ptr ↦ root_val ∗
      "Hxs" ∷ own xs' ∗
      "%HPerm1" ∷ ⌜xs ≡ₚ xs'⌝ ∗
      "%Hbound1" ∷ ⌜sint.Z lo ≤ sint.Z root_val ∧ sint.Z root_val < sint.Z hi⌝ ∗
      "%HSeg1" ∷ ⌜SegSortedFrom R xs' (sint.nat a) (sint.nat b) (sint.nat a + sint.nat hi)⌝ ∗
      "%He" ∷ ⌜HeapExcept R xs' (sint.nat a) (sint.nat lo) (sint.nat hi) (sint.nat root_val)⌝ ∗
      "%Hp" ∷ ⌜HeapParent R xs' (sint.nat a) (sint.nat lo) (sint.nat hi) (sint.nat root_val)⌝ ∗
      "%Hout" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ : IProp GF) $$ [root Hxs]
  · iexists lo, xs
    iframe
    ipureintro
    exact ⟨List.Perm.refl _, ⟨by omega, by omega⟩, HSegSorted, Hinit.1, Hinit.2,
      outsideSame_refl _ _ _⟩
  wp_for HI
  have HlenEq := HPerm1.length_eq
  obtain ⟨Hchild, Haroot, Hal⟩ := sift_arith1 a lo root_val hi b H_bounds.1 (by omega) Hbound1
    (by omega) (by omega)
  have ca := heap_sint_nat_cast a H_bounds.1
  have clo := heap_sint_nat_cast lo (by omega)
  have chi := heap_sint_nat_cast hi (by omega)
  have cb := heap_sint_nat_cast b (by omega)
  have croot := heap_sint_nat_cast root_val (by omega)
  have hHlen : sint.nat a + sint.nat hi ≤ xs'.length := by omega
  have hHB : sint.nat a + sint.nat hi ≤ sint.nat b := by omega
  have hBL : sint.nat b ≤ xs'.length := by omega
  have hLR : sint.nat lo ≤ sint.nat root_val := by omega
  have hrH : sint.nat root_val < sint.nat hi := by omega
  clear HlenEq Hinit HSegSorted Heap
  wp_if_destruct
  · -- `child ≥ hi`: break
    wp_for_post
    iapply HΦ
    iframe
    ipureintro
    refine ⟨HPerm1, HSeg1, ?_, Hout⟩
    exact sift_inv_close R xs' _ _ _ _ _ He (fun c _ _ hc hcH => by
      exfalso; omega)
  · have hrc : 2 * sint.nat root_val + 1 < sint.nat hi := by omega
    obtain ⟨Hr2, Halr, Har⟩ := sift_arith2 a lo root_val hi b H_bounds.1 (by omega)
      ⟨Hbound1.1, by omega⟩ (by omega) (by omega)
    obtain ⟨kc1, kal, karoot⟩ := heap_child_facts a root_val _ _ ca croot Hchild Hal Haroot
    obtain ⟨kc2, kalr, kar⟩ := heap_rchild_facts a root_val _ _ ca croot Hr2 Halr Har
    have hrA : sint.nat a + (2 * sint.nat root_val + 1) < xs'.length :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left hrc _) hHlen
    have hrtL : sint.nat a + sint.nat root_val < xs'.length :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left hrH _) hHlen
    obtain ⟨xl, Hxl⟩ := list_lookup_lt xs' _ hrA
    -- choose the greatest child `c` (three cases), joined at `Hsel`
    wp_join iprop(∃ (c : w64),
        "child" ∷ child_ptr ↦ c ∗
        "Hxs" ∷ own xs' ∗
        "first" ∷ first_ptr ↦ a ∗
        "data" ∷ data_ptr ↦ (interface.ok x : GoInterface) ∗
        "%Hsel" ∷ ⌜∃ cN : Nat, sint.nat c = cN ∧ sint.Z c = cN ∧
          (cN = 2 * sint.nat root_val + 1 ∨ cN = 2 * sint.nat root_val + 2) ∧ cN < sint.nat hi ∧
          MaxChild R xs' (sint.nat a) (sint.nat root_val) (sint.nat hi) cN ∧
          sint.Z (a + c) = ((sint.nat a + cN : Nat) : Int)⌝)
      with [child Hxs first data] as ⟨%c, child, Hxs, first, data, %Hsel⟩
    · -- the right child is in bounds: compare the children
      have hrc2 : 2 * sint.nat root_val + 2 < sint.nat hi := by omega
      have hrR : sint.nat a + (2 * sint.nat root_val + 2) < xs'.length :=
        Nat.lt_of_lt_of_le (Nat.add_lt_add_left hrc2 _) hHlen
      obtain ⟨xr', Hxr'⟩ := list_lookup_lt xs' (sint.nat a + (2 * sint.nat root_val + 2)) hrR
      have Hxl' := Hxl; rw [← heap_nat_eq _ _ kal] at Hxl'
      have Hxr'' := Hxr'; rw [← heap_nat_eq _ _ kalr] at Hxr''
      wp_apply wp_sorter_Less x own R xs' _ _ xl xr' (by omega) (by omega) Hxl' Hxr''
        $$ [$Hsrt $Hxs] as %r1 ⟨Hxs, %Hr1⟩
      cases r1
      · -- the left child is not smaller
        (try bool_if)
        wp_auto
        wp_join_done
        iexists _
        iframe
        ipureintro
        exact ⟨2 * sint.nat root_val + 1, heap_nat_eq _ _ kc1, kc1, Or.inl rfl, hrc,
          maxChild_left R xs' _ _ _ xl xr' Hxl Hxr' (fun h => by simpa using Hr1.2 h),
          kal⟩
      · -- the right child is greater
        (try bool_if)
        wp_auto
        wp_join_done
        iexists _
        iframe
        ipureintro
        exact ⟨2 * sint.nat root_val + 2, heap_nat_eq _ _ kc2, kc2, Or.inr rfl, hrc2,
          maxChild_right R xs' _ _ _ xl xr' Hxl Hxr' (Hr1.1 rfl), kar⟩
    · -- the right child is out of bounds: only the left child
      iexists _
      iframe
      ipureintro
      exact ⟨2 * sint.nat root_val + 1, heap_nat_eq _ _ kc1, kc1, Or.inl rfl, hrc,
        maxChild_only R xs' _ _ _ (by omega), kal⟩
    clear Hr2 Halr Har Hal Hchild Hxl xl kc1 kal kc2 kalr kar
    obtain ⟨cN, hcN, hcZ, hcsel, hcH, Hmax, hcidx⟩ := Hsel
    have hcL : sint.nat a + cN < xs'.length := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hcH _) hHlen
    obtain ⟨xrt, Hxrt⟩ := list_lookup_lt xs' (sint.nat a + sint.nat root_val) hrtL
    obtain ⟨xc, Hxc⟩ := list_lookup_lt xs' (sint.nat a + cN) hcL
    have Hxrt' := Hxrt; rw [← heap_nat_eq _ _ karoot] at Hxrt'
    have Hxc' := Hxc; rw [← heap_nat_eq _ _ hcidx] at Hxc'
    wp_apply wp_sorter_Less x own R xs' _ _ xrt xc (by omega) (by omega) Hxrt' Hxc'
      $$ [$Hsrt $Hxs] as %r2 ⟨Hxs, %Hr2'⟩
    cases r2
    · -- the root dominates its children: return
      (try bool_if)
      wp_auto
      wp_for_post
      iapply HΦ
      iframe
      ipureintro
      refine ⟨HPerm1, HSeg1, ?_, Hout⟩
      exact sift_inv_close R xs' _ _ _ _ _ He (fun c' x1 x2 hc' hc'H h1 h2 => by
        rw [Hxrt] at h1; cases h1
        have h3 : ¬ R xrt xc := fun h => by simpa using Hr2'.2 h
        exact notR_trans R x2 xc xrt h3 (Hmax c' xc x2 hc' hc'H Hxc h2))
    · -- the root is smaller than the child: swap and continue
      (try bool_if)
      wp_auto
      wp_apply wp_sorter_Swap x own R xs' _ _ xrt xc (by omega) (by omega) Hxrt' Hxc'
        $$ [$Hsrt $Hxs] as Hxs
      rw [heap_nat_eq _ _ karoot, heap_nat_eq _ _ hcidx,
        ← swap_set_comm xs' _ _ xrt xc Hxrt Hxc]
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      rw [hcN]
      have Hlt' : R xrt xc := Hr2'.1 rfl
      have Hstep := sift_inv_step R xs' (sint.nat a) (sint.nat lo) (sint.nat hi) (sint.nat root_val)
        cN xrt xc hLR hrH hcsel hcH hHlen Hxrt Hxc Hlt'
        (fun c' xc' h1 h2 h3 => Hmax c' xc xc' h1 h2 Hxc h3) He Hp
      have hAc : sint.nat a ≤ sint.nat a + cN := Nat.le_add_right _ _
      have hAr : sint.nat a ≤ sint.nat a + sint.nat root_val := Nat.le_add_right _ _
      have hrj : sint.nat a + sint.nat root_val < sint.nat a + sint.nat hi :=
        Nat.add_lt_add_left hrH _
      have hcj : sint.nat a + cN < sint.nat a + sint.nat hi := Nat.add_lt_add_left hcH _
      refine ⟨HPerm1.trans (swap_perm xs' _ _ xc xrt Hxc Hxrt), heap_new_root_bounds clo chi croot
          hcZ hcsel hcH hLR, ?_, Hstep.1, Hstep.2, ?_⟩
      · exact seg_sorted_swap R xs' _ _ _ _ _ xc xrt ⟨hAc, hcj⟩ ⟨hAr, hrj⟩
          hHB hBL Hxc Hxrt HSeg1
      · exact outsideSame_trans _ _ _ _ _ Hout
          (outsideSame_swap xs' _ _ xc xrt _ _ ⟨hAc, Nat.lt_of_lt_of_le hcj hHB⟩
            ⟨hAr, Nat.lt_of_lt_of_le hrj hHB⟩)

omit [StrictWeakOrder R] in
private theorem wp_siftDown_trivial (a b : w64) (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        "Hxs" ∷ own xs ∗
        "%H_bounds" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z b ≤ xs.length ∧ xs.length ≤ 2 ^ 62⌝ }}
      (App (App (App (App (Val (@! siftDown)) (Val #(interface.ok x))) (Val #(W64 0)))
        (Val #(W64 0))) (Val #a))
    {{ RET #(); "Hxs" ∷ own xs }} := by
  wp_start as H
  iNamed H
  wp_auto
  wp_for
  wp_for_post
  iapply HΦ
  iframe

set_option maxHeartbeats 1000000 in
theorem wp_heapSort (a b : w64) (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        "Hxs" ∷ own xs ∗
        "#Hsrt" ∷ isSorter x own R ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ }}
      (App (App (App (Val (@! heapSort)) (Val #(interface.ok x))) (Val #a)) (Val #b))
    {{ (xs' : List E), RET #();
        own xs' ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Hsorted" ∷ ⌜IsSortedSeg R xs' (sint.nat a) (sint.nat b)⌝ ∗
        "%Houtside" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ }} := by
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
      "Hxs" ∷ own xs' ∗
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
    wp_apply wp_siftDown x own R i_val (b - a) a b xs' $$ [Hxs]
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
        "Hxs" ∷ own xs' ∗
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
    · obtain ⟨xi, Hxi⟩ := list_lookup_lt xs' (sint.nat a + sint.nat i_val) (by word)
      obtain ⟨x0, Hx0⟩ := list_lookup_lt xs' (sint.nat a) (by word)
      have Hxi' : xs'[sint.nat (a + i_val)]? = some xi := by
        rw [show sint.nat (a + i_val) = sint.nat a + sint.nat i_val by word]; exact Hxi
      wp_apply wp_sorter_Swap x own R xs' a (a + i_val) x0 xi (by word) (by word) Hx0 Hxi'
        $$ [$Hsrt $Hxs] as Hxs
      rw [show sint.nat (a + i_val) = sint.nat a + sint.nat i_val by word,
        ← swap_set_comm xs' _ _ x0 xi Hx0 Hxi]
      by_cases hz : sint.Z i_val = 0
      · -- `i = 0`: the swap is trivial
        have hz' : i_val = W64 0 := BitVec.toInt_inj.mp (hz.trans (by decide))
        subst hz'
        have e0 : sint.nat (W64 0) = 0 := by decide
        rw [e0, Nat.add_zero] at Hxi
        rw [Hx0] at Hxi; cases Hxi
        rw [e0, Nat.add_zero, list_insert_id (list_lookup_insert_eq _ (by word)), list_insert_id Hx0]
        wp_apply wp_siftDown_trivial x own a b xs' $$ [Hxs] with Hxs
        · iframe Hxs; ipureintro; exact ⟨by word, by word, by word⟩
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
        wp_apply wp_siftDown x own R (W64 0) i_val a b
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

end sort

end Perennial
end
