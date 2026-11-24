/-
The proof of `internal.reflectlite.Value.Type`.
-/
module

public import Perennial.Spec.internal.reflectlite.Value__Type
public import Perennial.Spec.internal.reflectlite.toRType

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.reflectlite.Assumptions]

theorem internal.reflectlite.Value.Type.wp_proof
    (wp_toRType : internal.reflectlite.toRType.spec (GF := GF) (hG := hG)) :
    internal.reflectlite.Value.Type.spec (GF := GF) (hG := hG) := fun v hv => by
  wp_start as #Hinit
  wp_auto
  wp_if_destruct
  · exact absurd Hif hv
  wp_meths
  wp_apply wp_toRType
  iapply HΦ
  itrivial

end proof

end Perennial
