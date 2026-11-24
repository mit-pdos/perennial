/-
The proof of `internal.reflectlite.TypeOf`.
-/
module

public import Perennial.Spec.internal.reflectlite.TypeOf
public import Perennial.Spec.internal.reflectcore.TokOf
public import Perennial.Spec.internal.reflectlite.isModelRType
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

theorem internal.reflectlite.TypeOf.wp_proof
    (wp_TokOf : internal.reflectcore.TokOf.spec (GF := GF) (hG := hG))
    (wp_isModelRType : internal.reflectlite.isModelRType.spec (GF := GF) (hG := hG))
    (wp_toRType : internal.reflectlite.toRType.spec (GF := GF) (hG := hG)) :
    internal.reflectlite.TypeOf.spec (GF := GF) (hG := hG) := by
  constructor
  · intro t u hu k v hk hlen hr
    wp_start as #Hinit
    wp_auto
    wp_apply wp_TokOf
    unfold go.tok
    wp_apply wp_isModelRType k null hk hlen
    rw [hr]
    wp_auto
    wp_apply wp_toRType
    iapply HΦ
    itrivial
  · wp_start as #Hinit
    wp_auto
    iapply HΦ
    itrivial

end proof

end Perennial
