/-
The proof of `slices.medianAdjacentCmpFunc`.
-/
module

public import Perennial.Spec.slices.medianAdjacentCmpFunc
public import Perennial.Spec.slices.medianCmpFunc
public import Perennial.Proof.slices.PartitionBasics

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

theorem slices.medianAdjacentCmpFunc.wp_proof
    (wp_medianCmpFunc : slices.medianCmpFunc.spec (GF := GF) (hG := hG)) :
    slices.medianAdjacentCmpFunc.spec (GF := GF) (hG := hG) := by
  intro E _ _ Et _ R _ data a swaps_l cmp_code dq xs swaps
  wp_start as H
  iNamed H
  wp_auto
  wp_apply wp_medianCmpFunc R data (a - W64 1) a (a + W64 1) swaps_l cmp_code dq xs swaps
    $$ [Hxs Hswaps] with %r %sw ⟨Hxs, %Hr, Hswaps⟩
  · iframe; iframe #; ipureintro; word
  iapply HΦ; iframe; ipureintro
  rcases Hr with rfl | rfl | rfl <;> word

end proof

end Perennial
