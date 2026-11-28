/-
The proof of `internal.reflectcore.TypeIdentByName`.
-/
module

public import Perennial.Spec.internal.reflectcore.TypeIdentByName

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

theorem internal.reflectcore.TypeIdentByName.wp_proof :
    internal.reflectcore.TypeIdentByName.spec (GF := GF) (hG := hG) := fun T l => by
  wp_start
  wp_apply wp_TypeQuery "TypeQuery.identByName" .identByName rfl T l (W64 0) #(go.identByName T)
    (by unfold go.typeQuery; split <;> simp_all)
  iapply HΦ
  itrivial

end proof

end Perennial
