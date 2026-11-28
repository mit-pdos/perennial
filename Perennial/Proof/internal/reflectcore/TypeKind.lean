/-
The proof of `internal.reflectcore.TypeKind`.
-/
module

public import Perennial.Spec.internal.reflectcore.TypeKind

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

theorem internal.reflectcore.TypeKind.wp_proof :
    internal.reflectcore.TypeKind.spec (GF := GF) (hG := hG) := fun k l hk => by
  wp_start
  wp_apply wp_TypeQuery_kind k hk l (W64 0)
  iapply HΦ
  itrivial

end proof

end Perennial
