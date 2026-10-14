/-
The proof of `sort.Sort`.
-/
module

public import Perennial.Spec.sort.Sort
public import Perennial.Spec.sort.pdqsort
public import Perennial.Spec.math.bits.Len
public import Perennial.Proof.sort.SorterBasics
public import Perennial.Proof.slices.PdqSortBasics

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

theorem sort.«Sort».wp_proof
    (wp_pdqsort : sort.pdqsort.spec (GF := GF) (hG := hG))
    (wp_Len : math.bits.Len.spec (GF := GF) (hG := hG)) :
    sort.«Sort».spec (GF := GF) (hG := hG) := fun {E} x own R SWO xs => by
  -- (`fun`, not `intro`: `wp_apply_post` runs `whnfR` outside the goal's context, so a
  -- `wp_apply` fails silently on binders introduced by a tactic)
  wp_start as H
  iNamed H
  wp_auto
  wp_apply wp_sorter_Len x own R xs $$ [$Hsrt $Hxs] as Hxs
  have hn : sint.Z (W64 xs.length) = xs.length := by word
  wp_if_destruct
  · iapply HΦ
    iframe Hxs
    ipureintro
    refine ⟨List.Perm.refl _, fun i j xi xj Hi Hj Hij => ?_⟩
    have := lookup_lt_Some Hj
    have : xs.length ≤ 1 := by word
    omega
  wp_apply wp_Len with %l _
  wp_apply wp_pdqsort x own R (W64 0) (W64 xs.length) l xs $$ [Hxs]
    with %xs' ⟨Hxs, %Hperm, %Hsorted, %Houtside⟩
  · iframe Hxs; iframe #; ipureintro
    refine ⟨⟨by word, by word, by word, Hlength_bound⟩, ?_⟩
    unfold header; simp
  iapply HΦ
  iframe Hxs
  ipureintro
  refine ⟨Hperm, ?_⟩
  intro i j xi xj Hi Hj Hij
  apply isSortedSeg_is_sorted R xs' _ i j xi xj Hij Hi Hj
  rw [← Hperm.length_eq]
  rw [show sint.nat (W64 xs.length) = xs.length by word,
    show sint.nat (W64 0) = 0 by word] at Hsorted
  exact Hsorted

end proof

end Perennial
