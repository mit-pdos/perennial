/-
The proof of `slices.siftDownCmpFunc`.
-/
module

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

theorem slices.siftDownCmpFunc.wp_proof : slices.siftDownCmpFunc.spec (GF := GF) (hG := hG) := by
  constructor
  · intro E _ _ Et _ R _ data lo hi a b cmp_code xs
    wp_start as H
    iNamed H
    wp_auto
    unfold cmpImplements
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
          "cmp" ∷ cmp_ptr ↦ cmp_code ∗
          "first" ∷ first_ptr ↦ a ∗
          "data" ∷ data_ptr ↦ data ∗
          "%Hsel" ∷ ⌜∃ cN : Nat, sint.nat c = cN ∧ sint.Z c = cN ∧
            (cN = 2 * sint.nat root_val + 1 ∨ cN = 2 * sint.nat root_val + 2) ∧ cN < sint.nat hi ∧
            MaxChild R xs' (sint.nat a) (sint.nat root_val) (sint.nat hi) cN ∧
            sint.Z (a + c) = ((sint.nat a + cN : Nat) : Int)⌝)
        with [child Hxs cmp first data] as ⟨%c, child, Hxs, cmp, first, data, %Hsel⟩
      · -- the right child is in bounds: compare the children
        have hrc2 : 2 * sint.nat root_val + 2 < sint.nat hi := by omega
        have hrR : sint.nat a + (2 * sint.nat root_val + 2) < xs'.length :=
          Nat.lt_of_lt_of_le (Nat.add_lt_add_left hrc2 _) hHlen
        have kxr := heap_idx _ _ _ _ kalr hdl hrR
        obtain ⟨xr', Hxr'⟩ := list_lookup_lt xs' (sint.nat a + (2 * sint.nat root_val + 2)) hrR
        heap_load_k Hxl kxl
        heap_load_k Hxr' kxr
        wp_apply Hcmp with %r1 %Hr1
        wp_if_destruct
        · -- the right child is greater
          wp_join_done
          iexists _
          iframe
          ipureintro
          exact ⟨2 * sint.nat root_val + 2, heap_nat_eq _ _ kc2, kc2, Or.inr rfl, hrc2,
            maxChild_right R xs' _ _ _ xl xr' Hxl Hxr' (Hr1.1 (by omega)), kar⟩
        · -- the left child is not smaller
          wp_join_done
          iexists _
          iframe
          ipureintro
          exact ⟨2 * sint.nat root_val + 1, heap_nat_eq _ _ kc1, kc1, Or.inl rfl, hrc,
            maxChild_left R xs' _ _ _ xl xr' Hxl Hxr' (fun h => Hif (by have := Hr1.2 h; omega)),
            kal⟩
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
      wp_apply Hcmp with %r2 %Hr2'
      by_cases hlt : sint.Z r2 < sint.Z (W64 0)
      · -- the root is smaller than the child: swap and continue
        simp only [decide_eq_true hlt, Bool.not_true]
        wp_auto
        heap_slice_index_k kxrt
        wp_auto
        heap_slice_index_k kxc
        wp_auto
        heap_load_k Hxc kxc
        heap_load_k Hxrt kxrt
        wp_pures
        wp_apply wp_store_slice_index (t := Et) data _ xs' xc $$ [Hxs] with Hxs
        · iframe Hxs; ipureintro; exact kxrt.2.2
        rw [hridx]
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
        have Hlt' : R xrt xc := Hr2'.1 (by omega)
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
        simp only [decide_eq_false hlt, Bool.not_false]
        wp_auto
        wp_for_post
        iapply HΦ
        iframe
        ipureintro
        refine ⟨HPerm1, HSeg1, ?_, Hout⟩
        exact sift_inv_close R xs' _ _ _ _ _ He (fun c' x1 x2 hc' hc'H h1 h2 => by
          rw [Hxrt] at h1; cases h1
          have h3 : ¬ R xrt xc := fun h => hlt (by have := Hr2'.2 h; omega)
          exact notR_trans R x2 xc xrt h3 (Hmax c' xc x2 hc' hc'H Hxc h2))
  · intro E _ _ Et _ R _ data a b cmp_code xs
    wp_start as H
    iNamed H
    wp_auto
    wp_for
    wp_for_post
    iapply HΦ
    iframe

end proof

end Perennial
