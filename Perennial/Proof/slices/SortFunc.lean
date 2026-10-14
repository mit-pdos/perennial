/-
The proof of `slices.SortFunc`.
-/
module

public import Perennial.Spec.slices.SortFunc
public import Perennial.Spec.math.bits.Len
public import Perennial.Spec.slices.pdqsortCmpFunc
public import Perennial.Proof.slices.PdqSortBasics
public import Perennial.Proof.slices.OrderedBasics

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

theorem slices.SortFunc.wp_proof
    (wp_Len : math.bits.Len.spec (GF := GF) (hG := hG))
    (wp_pdqsortCmpFunc : slices.pdqsortCmpFunc.spec (GF := GF) (hG := hG)) :
    slices.SortFunc.spec (GF := GF) (hG := hG) := by
  intro E _ _ Et _ R S _ data cmp_code xs SWO
  wp_start as H
  iNamed H
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hxs
  wp_apply wp_Len with %l _
  wp_apply wp_pdqsortCmpFunc R data (W64 0) data.len l cmp_code xs $$ [Hxs]
    with %xs' ⟨Hxs, %Hperm, %Hsorted, %Houtside⟩
  · iframe Hxs; iframe #; ipureintro
    refine ⟨by word, ?_⟩
    unfold header; simp
  iapply HΦ
  iframe Hxs
  ipureintro
  refine ⟨Hperm, ?_⟩
  intro i j xi xj Hi Hj Hij
  apply isSortedSeg_is_sorted R xs' _ i j xi xj Hij Hi Hj
  rw [← Hperm.length_eq, Hlen.1]
  exact Hsorted

end proof

end Perennial
