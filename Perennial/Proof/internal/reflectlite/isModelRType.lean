/-
The proof of `internal.reflectlite.isModelRType`.
-/
module

public import Perennial.Spec.internal.reflectlite.isModelRType
public import Perennial.Spec.internal.reflectcore.TypeKind

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

theorem internal.reflectlite.isModelRType.wp_proof
    (wp_TypeKind : internal.reflectcore.TypeKind.spec (GF := GF) (hG := hG)) :
    internal.reflectlite.isModelRType.spec (GF := GF) (hG := hG) := @fun T u _ k l h hk => by
  wp_start as #Hinit
  wp_auto
  wp_apply wp_TypeKind k l h
  simp only [internal.reflectlite.kind_ne_struct h hk, decide_false]
  wp_auto
  iapply HΦ
  itrivial

end proof

end Perennial
