/-
The proof of `internal.reflectcore.assertOk`.
-/
module

public import Perennial.Spec.internal.reflectcore.assertOk_

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

theorem internal.reflectcore.assertOk.wp_proof :
    internal.reflectcore.assertOk.spec (GF := GF) (hG := hG) := by
  intro T elems _ x
  wp_start
  wp_auto
  cases x <;> wp_auto <;> iapply HΦ <;> itrivial

end proof

end Perennial
