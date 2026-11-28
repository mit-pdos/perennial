/-
The proof of `internal.reflectcore.TokOf`.
-/
module

public import Perennial.Spec.internal.reflectcore.TokOf
public import Perennial.Spec.internal.reflectcore.tokOf_

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

theorem internal.reflectcore.TokOf.wp_proof
    (wp_tokOf : internal.reflectcore.tokOf.spec (GF := GF) (hG := hG)) :
    internal.reflectcore.TokOf.spec (GF := GF) (hG := hG) := fun t v => by
  wp_start
  wp_apply wp_FuncResolveAt go.Shape.self _ t v [t] rfl
  rw [show (go!"internal/reflectcore.tokOf" : GoString) = tokOf from rfl]
  wp_apply wp_tokOf
  iapply HΦ
  itrivial

end proof

end Perennial
