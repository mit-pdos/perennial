/-
The proof of `internal.reflectcore.TypeUnderlying`.
-/
module

public import Perennial.Spec.internal.reflectcore.TypeUnderlying

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

theorem internal.reflectcore.TypeUnderlying.wp_proof :
    internal.reflectcore.TypeUnderlying.spec (GF := GF) (hG := hG) := fun T l => by
  wp_start
  wp_apply wp_TypeQuery .underlying T l (W64 0) #(go.tok (underlying T))
    (by unfold go.typeQuery; split <;> simp_all)
  iapply HΦ
  itrivial

end proof

end Perennial
