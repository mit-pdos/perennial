/-
The proof of `slices.medianAdjacentOrdered`.
-/
module

public import Perennial.Spec.slices.medianAdjacentOrdered
public import Perennial.Spec.slices.medianOrdered
public import Perennial.Proof.slices.OrderedPartitionBasics

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

theorem slices.medianAdjacentOrdered.wp_proof
    (wp_medianOrdered : slices.medianOrdered.spec (GF := GF) (hG := hG)) :
    slices.medianAdjacentOrdered.spec (GF := GF) (hG := hG) := by
  intro E _ _ Et _ R _ data a swaps_l dq xs swaps
  wp_start as H
  iNamed H
  wp_auto
  wp_apply wp_medianOrdered R data (a - W64 1) a (a + W64 1) swaps_l dq xs swaps
    $$ [Hxs Hswaps] with %r %sw ⟨Hxs, %Hr, Hswaps⟩
  · iframe; iframe #; ipureintro; word
  iapply HΦ; iframe; ipureintro
  rcases Hr with rfl | rfl | rfl <;> word

end proof

end Perennial
