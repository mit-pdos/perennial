/-
The proof of `sort.partition` over a `sort.Interface`: the proof of `slices.partitionCmpFunc`
(`Perennial/Proof/slices/partitionCmpFunc.lean`) with `Less`/`Swap` calls.
-/
module

public import Perennial.Spec.sort.partition
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

theorem sort.partition.wp_proof : sort.partition.spec (GF := GF) (hG := hG) := fun {E} x own R _ a b pivot xs => by
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
  ihave HI : partInv own R a b xp xs i_ptr j_ptr false false $$ [Hxs i j]
  · unfold partInv
    iexists _, _, _
    iframe
    ipureintro
    refine ⟨by word, ?_, ?_, ?_, ?_, by simp, by simp⟩
    · intro i xi xa' _ _; constructor <;> intro <;> word
    · by_cases h : sint.nat pivot = sint.nat a
      · rw [h, list_lookup_insert_eq _ (by simp; word)]
        rw [h, Hxa_lookup] at Hxp_lookup; exact Hxp_lookup
      · rw [list_lookup_insert_ne _ _ h, list_lookup_insert_eq _ (by word)]
    · exact swap_perm xs _ _ xp xa Hxp_lookup Hxa_lookup
    · exact outsideSame_swap _ _ _ _ _ _ _ (by word) (by word)
  part_loop1
  part_loop2
  part_load_j
  wp_if_destruct
  · part_finish
  · part_swap
    clear Hpart Hpivot HPerm1 Houtside1 HBr1 HBr2 HBr1' HBr2' Hlen2 Hxi_lookup Hxj_lookup ij_bound Hif Hle
      xs1 i_val j_val xi xj
    wp_for
    part_loop1
    part_loop2
    part_load_j
    wp_if_destruct
    · wp_for_post
      part_finish
    · part_swap
      wp_for_post
      unfold partInv
      simp only [Bool.false_eq_true]
      iframe

end proof

end Perennial
