/-
The proof of `internal.reflectcore.TypeElem`.
-/
module

public import Perennial.Spec.internal.reflectcore.TypeElem

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

theorem internal.reflectcore.TypeElem.wp_proof :
    internal.reflectcore.TypeElem.spec (GF := GF) (hG := hG) := fun T l v h => by
  wp_start
  wp_apply wp_TypeQuery _ T l (W64 0) v h
  iapply HΦ
  itrivial

end proof

end Perennial
