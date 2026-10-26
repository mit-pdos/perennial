/-
The proof of `sort.siftDown` over a `sort.Interface`: the proof of `slices.siftDownCmpFunc`
(`Perennial/Proof/slices/siftDownCmpFunc.lean`) with `Less`/`Swap` calls.
-/
module

public import Perennial.Spec.sort.siftDown
public import Perennial.Proof.sort.SorterBasics
public import Perennial.Proof.slices.HeapSortBasics

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open slices

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

set_option maxHeartbeats 1000000 in
theorem sort.siftDown.wp_proof : sort.siftDown.spec (GF := GF) (hG := hG) :=
  -- (`fun`, not `intro`: `wp_apply_post` runs `whnfR` outside the goal's context, so a
  -- `wp_apply` fails silently on binders introduced by a tactic)
  And.intro
    (fun {E} x own R _ lo hi a b xs => by
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
                ⟨hAr, Nat.lt_of_lt_of_le hrj hHB⟩))
    (fun {E} x own a b xs => by
      wp_start as H
      iNamed H
      wp_auto
      wp_for
      wp_for_post
      iapply HΦ
      iframe)

end proof

end Perennial
