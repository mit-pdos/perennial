/-
The proof of `sort.partitionEqual` over a `sort.Interface`: the proof of `slices.partitionEqualCmpFunc`
(`Perennial/Proof/slices/partitionEqualCmpFunc.lean`) with `Less`/`Swap` calls.
-/
module

public import Perennial.Spec.sort.partitionEqual
public import Perennial.Proof.sort.SorterBasics
public import Perennial.Proof.slices.PartitionBasics
public import Perennial.Proof.sort.PartitionBasics

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

theorem sort.partitionEqual.wp_proof : sort.partitionEqual.spec (GF := GF) (hG := hG) := fun {E} x own R _ a b pivot xs => by
  -- (`fun`, not `intro`: `wp_apply_post` runs `whnfR` outside the goal's context, so a
  -- `wp_apply` fails silently on binders introduced by a tactic)
  wp_start as H
  iNamed H
  wp_auto
  list_elem xs (sint.nat pivot) as xp
  list_elem xs (sint.nat a) as xa
  wp_apply wp_sorter_Swap_raw x own R xs a pivot xa xp (by omega) (by omega)
    Hxa_lookup Hxp_lookup $$ [$Hsrt $Hxs] as Hxs
  (try wp_auto)
  ipersist a
  ipersist data
  ihave HI : peqInv own R a b xp xs i_ptr j_ptr false false $$ [Hxs i j]
  · unfold peqInv
    iexists _, _, _
    iframe
    ipureintro
    refine ⟨by word, ?_, ?_, ?_, swap_perm xs _ _ xp xa Hxp_lookup Hxa_lookup,
      outsideSame_swap _ _ _ _ _ _ _ (by word) (by word), by simp, by simp⟩
    · intro i j xi xj hb; word
    · by_cases h : sint.nat pivot = sint.nat a
      · rw [h, list_lookup_insert_eq _ (by simp; word)]
        rw [h, Hxa_lookup] at Hxp_lookup; exact Hxp_lookup
      · rw [list_lookup_insert_ne _ _ h, list_lookup_insert_eq _ (by word)]
    · exact peq_init_min R xs _ _ _ xp xa Hxp_lookup Hxa_lookup ⟨by word, by word⟩ Hmin
  wp_for
  -- first inner loop: `for i <= j && !data.Less(a, i) { i++ }`
  wp_bind (App (App (App (Val doFor) _) _) _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
    peqInv own R a b xp xs i_ptr j_ptr true false))) $$ [HI]
  · unfold peqInv
    wp_for HI
    have Hlen2 := HPerm1.length_eq
    wp_if_destruct
    · list_elem xs1 (sint.nat i_val) as xi
      wp_apply wp_sorter_Less x own R xs1 a i_val xp xi (by word) (by word) Hpivot Hxi_lookup
        $$ [$Hsrt $Hxs] as %r ⟨Hxs, %Hr⟩
      cases r
      · bool_if'
        wp_auto
        wp_for_post
        iframe
        iexists xs1, (i_val + W64 1), j_val
        iframe
        ipureintro
        refine ⟨by word, ?_, Hpivot, Hmin, HPerm1, Houtside1, nofun, nofun⟩
        rw [show sint.nat (i_val + W64 1) = sint.nat i_val + 1 by word]
        exact isEqSeg_extend R xs1 _ _ xp xi Hpivot Hsorted Hxi_lookup
          ⟨Hmin xp _ xi ⟨by word, by word⟩ Hpivot Hxi_lookup,
           fun h => by simpa using Hr.2 h⟩
      · bool_if'
        isplitl []
        · itrivial
        iexists xs1, i_val, j_val
        iframe
        ipureintro
        refine ⟨ij_bound, Hsorted, Hpivot, Hmin, HPerm1, Houtside1, fun _ => Or.inr ?_, nofun⟩
        intro xi' hxi'
        rw [Hxi_lookup] at hxi'; cases hxi'
        exact R_antisym R _ _ (Hr.1 rfl)
    · isplitl []
      · itrivial
      iexists xs1, i_val, j_val
      iframe
      ipureintro
      exact ⟨ij_bound, Hsorted, Hpivot, Hmin, HPerm1, Houtside1, fun _ => Or.inl (by omega),
        nofun⟩
  iintro %v ⟨%Hv, HI⟩
  subst Hv
  (try wp_auto)
  -- second inner loop: `for i <= j && data.Less(a, j) { j-- }`
  wp_bind (App (App (App (Val doFor) _) _) _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
    peqInv own R a b xp xs i_ptr j_ptr true true))) $$ [HI]
  · unfold peqInv
    wp_for HI
    have Hlen2 := HPerm1.length_eq
    wp_if_destruct
    · list_elem xs1 (sint.nat j_val) as xj
      wp_apply wp_sorter_Less x own R xs1 a j_val xp xj (by word) (by word) Hpivot Hxj_lookup
        $$ [$Hsrt $Hxs] as %r ⟨Hxs, %Hr⟩
      cases r
      · bool_if'
        isplitl []
        · itrivial
        iexists xs1, i_val, j_val
        iframe
        ipureintro
        refine ⟨ij_bound, Hsorted, Hpivot, Hmin, HPerm1, Houtside1, fun _ => HBr1 rfl,
          fun _ => Or.inr ?_⟩
        intro xj' hxj'
        rw [Hxj_lookup] at hxj'; cases hxj'
        exact fun h => by simpa using Hr.2 h
      · bool_if'
        wp_auto
        wp_for_post
        iframe
        iexists xs1, i_val, (j_val - W64 1)
        iframe
        ipureintro
        refine ⟨by word, Hsorted, Hpivot, Hmin, HPerm1, Houtside1, fun _ => ?_, nofun⟩
        rcases HBr1 rfl with h | h
        · left; word
        · right; exact h
    · isplitl []
      · itrivial
      iexists xs1, i_val, j_val
      iframe
      ipureintro
      exact ⟨ij_bound, Hsorted, Hpivot, Hmin, HPerm1, Houtside1, fun _ => HBr1 rfl,
        fun _ => Or.inl (by omega)⟩
  iintro %v ⟨%Hv, HI⟩
  subst Hv
  (try wp_auto)
  unfold peqInv
  iNamed HI
  have Hlen2 := HPerm1.length_eq
  (try wp_auto)
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
    wp_apply wp_sorter_Swap_raw x own R xs1 i_val j_val xi xj (by word) (by word) Hxi_lookup
      Hxj_lookup $$ [$Hsrt $Hxs] as Hxs
    (try wp_auto)
    wp_for_post
    iframe
    iexists _, (i_val + W64 1), (j_val - W64 1)
    iframe
    ipureintro
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
