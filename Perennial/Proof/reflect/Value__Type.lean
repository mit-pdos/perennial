/-
The proof of `reflect.Value.Type`.
-/
module

public import Perennial.Spec.reflect.Value__Type
public import Perennial.Spec.reflect.toRType

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : reflect.Assumptions]

theorem reflect.Value.Type.wp_proof
    (wp_toRType : reflect.toRType.spec (GF := GF) (hG := hG)) :
    reflect.Value.Type.spec (GF := GF) (hG := hG) := fun v hv hm => by
  wp_start as #Hinit
  wp_auto
  wp_if_destruct
  · exact absurd Hif hv
  wp_if_destruct
  · wp_apply wp_toRType
    iapply HΦ
    itrivial
  · exact absurd hm Hif

end proof

end Perennial
