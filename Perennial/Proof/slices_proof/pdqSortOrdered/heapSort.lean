/-
Specs of `siftDownOrdered` and `heapSortOrdered`: the `Ordered` ports of the
`CmpFunc` proofs in `pdqSort/heapSort.lean` (all pure lemmas are reused).
-/
module

public import Perennial.Proof.slices_proof.pdqSortOrdered.ordered_basics
public import Perennial.Proof.slices_proof.pdqSort.heapSort

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace slices

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]
variable {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
  [IntoValTyped (GF := GF) E Et]
variable (R : E → E → Prop) [StrictWeakOrder R]

theorem wp_siftDownOrdered (data : GoSlice) (lo hi a b : w64) (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "#Hless" ∷ lessImplements (Et := Et) R ∗
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
      (App (App (App (App (Val #(functions siftDownOrdered [Et])) (Val #data)) (Val #lo))
        (Val #hi)) (Val #a))
    {{ (xs' : List E), RET #();
        "Hxs" ∷ data ↦* xs' ∗
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
  unfold lessImplements
  ihave %Hlen0 := ownSlice_len _ _ _ $$ Hxs
  have Hinit := sift_inv_init R xs (sint.nat a) (sint.nat b) (sint.nat lo) (sint.nat hi) Heap
  ihave HI : (∃ (root_val : w64) (xs' : List E),
      "root" ∷ root_ptr ↦ root_val ∗
      "Hxs" ∷ data ↦* xs' ∗
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
  ihave %Hlen := ownSlice_len _ _ _ $$ Hxs
  have HlenEq := HPerm1.length_eq
  obtain ⟨Hchild, Haroot, Hal⟩ := sift_arith1 a lo root_val hi b H_bounds.1 (by omega) Hbound1
    (by omega) (by omega)
  have h0 : sint.Z (W64 0) = 0 := by decide
  have hdl : sint.Z data.len = xs'.length := by iomega
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
  clear Hlen Hlen0 HlenEq Hinit HSegSorted Heap
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
    have kxl := heap_idx _ _ _ _ kal hdl hrA
    have kxrt := heap_idx _ _ _ _ karoot hdl hrtL
    have hridx : (sint.Z (a + root_val)).toNat = sint.nat a + sint.nat root_val := kxrt.2.1
    obtain ⟨xl, Hxl⟩ := list_lookup_lt xs' _ hrA
    -- choose the greatest child `c` (three cases), joined at `Hsel`
    wp_join iprop(∃ (c : w64),
        "child" ∷ child_ptr ↦ c ∗
        "Hxs" ∷ data ↦* xs' ∗
        "first" ∷ first_ptr ↦ a ∗
        "data" ∷ data_ptr ↦ data ∗
        "%Hsel" ∷ ⌜∃ cN : Nat, sint.nat c = cN ∧ sint.Z c = cN ∧
          (cN = 2 * sint.nat root_val + 1 ∨ cN = 2 * sint.nat root_val + 2) ∧ cN < sint.nat hi ∧
          MaxChild R xs' (sint.nat a) (sint.nat root_val) (sint.nat hi) cN ∧
          sint.Z (a + c) = ((sint.nat a + cN : Nat) : Int)⌝)
      with [child Hxs first data] as ⟨%c, child, Hxs, first, data, %Hsel⟩
    · -- the right child is in bounds: compare the children
      have hrc2 : 2 * sint.nat root_val + 2 < sint.nat hi := by omega
      have hrR : sint.nat a + (2 * sint.nat root_val + 2) < xs'.length :=
        Nat.lt_of_lt_of_le (Nat.add_lt_add_left hrc2 _) hHlen
      have kxr := heap_idx _ _ _ _ kalr hdl hrR
      obtain ⟨xr', Hxr'⟩ := list_lookup_lt xs' (sint.nat a + (2 * sint.nat root_val + 2)) hrR
      heap_load_k Hxl kxl
      heap_load_k Hxr' kxr
      wp_apply Hless with %r1 %Hr1
      wp_if_destruct
      · -- the left child is not smaller
        wp_join_done
        iexists _
        iframe
        ipureintro
        exact ⟨2 * sint.nat root_val + 1, heap_nat_eq _ _ kc1, kc1, Or.inl rfl, hrc,
          maxChild_left R xs' _ _ _ xl xr' Hxl Hxr' (fun h => absurd (Hr1.2 h) (by simp)),
          kal⟩
      · -- the right child is greater
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
    clear Hr2 Halr Har Hal Hchild Hxl xl kc1 kal kc2 kalr kar kxl
    obtain ⟨cN, hcN, hcZ, hcsel, hcH, Hmax, hcidx⟩ := Hsel
    have hcL : sint.nat a + cN < xs'.length := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hcH _) hHlen
    have kxc := heap_idx _ _ _ _ hcidx hdl hcL
    obtain ⟨xrt, Hxrt⟩ := list_lookup_lt xs' (sint.nat a + sint.nat root_val) hrtL
    obtain ⟨xc, Hxc⟩ := list_lookup_lt xs' (sint.nat a + cN) hcL
    heap_load_k Hxrt kxrt
    heap_load_k Hxc kxc
    wp_apply Hless with %r2 %Hr2'
    by_cases hlt : r2 = true
    · -- the root is smaller than the child: swap and continue
      subst hlt
      simp only [Bool.not_true]
      wp_auto
      heap_load_k Hxc kxc
      heap_load_k Hxrt kxrt
      heap_slice_index_k kxrt
      wp_pures
      wp_apply wp_store_slice_index (t := Et) data _ xs' xc $$ [Hxs] with Hxs
      · iframe Hxs; ipureintro; exact kxrt.2.2
      rw [hridx]
      heap_slice_index_k kxc
      wp_pures
      wp_apply wp_store_slice_index (t := Et) data _ (xs'.set (sint.nat a + sint.nat root_val) xc) xrt $$ [Hxs]
        with Hxs
      · iframe Hxs; ipureintro; refine ⟨kxc.2.2.1, ?_⟩; rw [List.length_set]; exact kxc.2.2.2
      rw [kxc.2.1]
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
    · -- the root dominates its children: return
      have hf : r2 = false := by simpa using hlt
      subst hf
      simp only [Bool.not_false]
      wp_auto
      wp_for_post
      iapply HΦ
      iframe
      ipureintro
      refine ⟨HPerm1, HSeg1, ?_, Hout⟩
      exact sift_inv_close R xs' _ _ _ _ _ He (fun c' x1 x2 hc' hc'H h1 h2 => by
        rw [Hxrt] at h1; cases h1
        have h3 : ¬ R xrt xc := fun h => absurd (Hr2'.2 h) (by simp)
        exact notR_trans R x2 xc xrt h3 (Hmax c' xc x2 hc' hc'H Hxc h2))

theorem wp_siftDownOrdered_Trivial (data : GoSlice) (a b : w64)
    (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "#Hless" ∷ lessImplements (Et := Et) R ∗
        "%H_bounds" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z b ≤ xs.length ∧ xs.length ≤ 2 ^ 62⌝ }}
      (App (App (App (App (Val #(functions siftDownOrdered [Et])) (Val #data))
        (Val #(W64 0))) (Val #(W64 0))) (Val #a))
    {{ RET #(); "Hxs" ∷ data ↦* xs }} := by
  wp_start as H
  iNamed H
  wp_auto
  wp_for
  wp_for_post
  iapply HΦ
  iframe

theorem wp_heapSortOrdered (data : GoSlice) (a b : w64) (xs : List E) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "#Hless" ∷ lessImplements (Et := Et) R ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ }}
      (App (App (App (Val #(functions heapSortOrdered [Et])) (Val #data)) (Val #a))
        (Val #b))
    {{ (xs' : List E), RET #();
        data ↦* xs' ∗
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
    wp_apply wp_siftDownOrdered R data i_val (b - a) a b xs' $$ [Hxs]
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
      heap_load_atw Hxi
      heap_load_atw Hx0
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by constructor <;> word))]
      wp_pures
      wp_apply wp_store_slice_index (t := Et) data _ xs' xi $$ [Hxs] with Hxs
      · iframe Hxs; ipureintro; constructor <;> word
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by constructor <;> word))]
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
        wp_apply wp_siftDownOrdered_Trivial R data a b xs' $$ [Hxs] with Hxs
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
        wp_apply wp_siftDownOrdered R data (W64 0) i_val a b
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

end slices

end Perennial
end
