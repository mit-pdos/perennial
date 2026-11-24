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
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.reflectcore.Assumptions]

theorem internal.reflectcore.EqNilAt.wp_proof :
    internal.reflectcore.EqNilAt.spec (GF := GF) (hG := hG) := by
  refine ⟨fun l => ?_, fun s => ?_, fun m => ?_, fun c => ?_, fun f => ?_⟩ <;> wp_start
  · iapply HΦ; itrivial
  · rw [show zero_val GoSlice = slice.nil from rfl]; wp_auto; iapply HΦ; itrivial
  · rw [show zero_val GoMap = map.nil from rfl]; wp_auto; iapply HΦ; itrivial
  · iapply HΦ; itrivial
  · rw [show zero_val GoFunc = func.nil from rfl]; wp_auto; iapply HΦ; itrivial

end proof

end Perennial
