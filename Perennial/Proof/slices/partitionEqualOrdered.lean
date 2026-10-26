/-
The proof of `slices.partitionEqualOrdered`.
-/
module

public import Perennial.Spec.slices.partitionEqualOrdered
public import Perennial.Proof.slices.OrderedPartitionBasics

@[expose] public section

set_option linter.iris.style.nameCheck false
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

theorem slices.partitionEqualOrdered.wp_proof : slices.partitionEqualOrdered.spec (GF := GF) (hG := hG) := by
  intro E _ _ Et _ R _ data a b pivot xs
  wp_start as H
  iNamed H
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hxs
  list_elem xs (sint.nat pivot) as xp
  list_elem xs (sint.nat a) as xa
  slice_index_if
  wp_auto
  slice_index_if
  wp_auto
  slice_index_if
  wp_apply wp_load_slice_index data (sint.Z pivot) xs _ xp (by omega) $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; exact Hxp_lookup
  slice_index_if
  wp_apply wp_load_slice_index data (sint.Z a) xs _ xa (by omega) $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; exact Hxa_lookup
  wp_pures
  wp_apply wp_store_slice_index data (sint.Z a) xs xp $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; omega
  wp_pures
  wp_apply wp_store_slice_index data (sint.Z pivot) _ xa $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; simp; omega
  wp_auto
  ipersist a
  ipersist data
  ihave HI : peqInv R data a b xp xs i_ptr j_ptr false false $$ [Hxs i j]
  · unfold peqInv
    iexists _, _, _
    iframe
    ipureintro
    simp only [sint_toNat]
    refine ⟨by word, ?_, ?_, ?_, swap_perm xs _ _ xp xa Hxp_lookup Hxa_lookup,
      outsideSame_swap _ _ _ _ _ _ _ (by word) (by word), by simp, by simp⟩
    · intro i j xi xj hb; word
    · by_cases h : sint.nat pivot = sint.nat a
      · rw [h, list_lookup_insert_eq _ (by simp; word)]
        rw [h, Hxa_lookup] at Hxp_lookup; exact Hxp_lookup
      · rw [list_lookup_insert_ne _ _ h, list_lookup_insert_eq _ (by word)]
    · exact peq_init_min R xs _ _ _ xp xa Hxp_lookup Hxa_lookup ⟨by word, by word⟩ Hmin
  wp_for
  -- first inner loop: `for i <= j && !less(data[a], data[i]) { i++ }`
  wp_bind (App (App (App (Val doFor) _) _) _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
    peqInv R data a b xp xs i_ptr j_ptr true false))) $$ [HI]
  · iapply (wp_peq_loop1_ord (Et := Et) R data a b xp xs i_ptr j_ptr data_ptr a_ptr
      Hab_bound Hlen) $$ Hpkg Hless a data HI
  iintro %v ⟨%Hv, HI⟩
  subst Hv
  wp_auto
  -- second inner loop: `for i <= j && less(data[a], data[j]) { j-- }`
  wp_bind (App (App (App (Val doFor) _) _) _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
    peqInv R data a b xp xs i_ptr j_ptr true true))) $$ [HI]
  · iapply (wp_peq_loop2_ord (Et := Et) R data a b xp xs i_ptr j_ptr data_ptr a_ptr
      Hab_bound Hlen) $$ Hpkg Hless a data HI
  iintro %v ⟨%Hv, HI⟩
  subst Hv
  wp_auto
  unfold peqInv
  iNamed HI
  have Hlen2 := HPerm1.length_eq
  wp_auto
  wp_if_destruct
  · -- break; return `i`
    wp_for_post
    iapply HΦ
    iframe Hxs
    ipureintro
    exact ⟨⟨by omega, by omega⟩, HPerm1, peq_conclude R xs1 _ _ _ xp Hpivot Hsorted Hmin,
      Houtside1⟩
  · have Hle : sint.Z i_val ≤ sint.Z j_val := by word
    list_elem xs1 (sint.nat j_val) as xj
    list_elem xs1 (sint.nat i_val) as xi
    have HBr1' := HBr1 rfl
    have HBr2' := HBr2 rfl
    slice_index_if
    wp_auto
    slice_index_if
    wp_auto
    slice_index_if
    wp_apply wp_load_slice_index data (sint.Z j_val) xs1 _ xj (by omega) $$ [Hxs] with Hxs
    · iframe Hxs; ipureintro; exact Hxj_lookup
    slice_index_if
    wp_apply wp_load_slice_index data (sint.Z i_val) xs1 _ xi (by omega) $$ [Hxs] with Hxs
    · iframe Hxs; ipureintro; exact Hxi_lookup
    wp_pures
    wp_apply wp_store_slice_index data (sint.Z i_val) xs1 xj $$ [Hxs] with Hxs
    · iframe Hxs; ipureintro; omega
    wp_pures
    wp_apply wp_store_slice_index data (sint.Z j_val) _ xi $$ [Hxs] with Hxs
    · iframe Hxs; ipureintro; simp; omega
    try wp_auto
    wp_for_post
    iframe
    iexists _, (i_val + W64 1), (j_val - W64 1)
    iframe
    ipureintro
    simp only [sint_toNat]
    have hbr2 : ¬ R xp xj := by
      rcases HBr2' with h | h
      · omega
      · exact h xj Hxj_lookup
    refine ⟨by word, ?_, ?_, ?_, HPerm1.trans (swap_perm xs1 _ _ xj xi Hxj_lookup Hxi_lookup), ?_,
      nofun, nofun⟩
    · rw [show sint.nat (i_val + W64 1) = sint.nat i_val + 1 by word]
      exact peq_swap_seg R xs1 _ _ _ _ xi xj xp Hxi_lookup Hxj_lookup Hpivot
        ⟨by word, by word, by word⟩ Hsorted Hmin hbr2
    · rw [list_lookup_insert_ne _ _ (by word), list_lookup_insert_ne _ _ (by word)]
      exact Hpivot
    · exact peq_swap_min R xs1 _ _ _ _ xi xj Hxi_lookup Hxj_lookup ⟨by word, by word, by word⟩ Hmin
    · exact outsideSame_trans _ _ _ _ _ Houtside1
        (outsideSame_swap _ _ _ _ _ _ _ (by word) (by word))

end proof

end Perennial
