/-
The proof of `internal.reflectcore.AssertOk`.
-/
module

public import Perennial.Spec.internal.reflectcore.AssertOk
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

theorem internal.reflectcore.AssertOk.wp_proof
    (wp_assertOk : internal.reflectcore.assertOk.spec (GF := GF) (hG := hG)) :
    internal.reflectcore.AssertOk.spec (GF := GF) (hG := hG) := by
  intro T elems _ l x
  wp_start
  wp_apply wp_FuncResolveAt (go.Shape.deref go.Shape.self) _ _ _ [T] rfl
  rw [show (go!"internal/reflectcore.assertOk" : GoString) = assertOk from rfl]
  wp_apply wp_assertOk x
  iapply HΦ
  itrivial

end proof

end Perennial
