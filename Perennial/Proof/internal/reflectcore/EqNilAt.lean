/-
The proof of `internal.reflectcore.EqNilAt`.
-/
module

public import Perennial.Spec.internal.reflectcore.EqNilAt

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [HasExt reflectExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.reflectcore.Assumptions]

theorem internal.reflectcore.EqNilAt.wp_proof :
    internal.reflectcore.EqNilAt.spec (GF := GF) (hG := hG) := by
  refine ⟨fun l => ?_, fun s => ?_, fun m => ?_, fun c => ?_, fun f => ?_⟩ <;> wp_start
  · wp_apply wp_EqNilAt_pointer l; iapply HΦ; itrivial
  · wp_apply wp_EqNilAt_slice s; iapply HΦ; itrivial
  · wp_apply wp_EqNilAt_map m; iapply HΦ; itrivial
  · wp_apply wp_EqNilAt_chan c; iapply HΦ; itrivial
  · wp_apply wp_EqNilAt_func f; iapply HΦ; itrivial

end proof

end Perennial
