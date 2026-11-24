/-
The proof of `internal.reflectlite.rtype.Kind`.
-/
module

public import Perennial.Spec.internal.reflectlite.rtype__Kind
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

theorem internal.reflectlite.rtype.Kind.wp_proof
    (wp_TypeKind : internal.reflectcore.TypeKind.spec (GF := GF) (hG := hG)) :
    internal.reflectlite.rtype.Kind.spec (GF := GF) (hG := hG) := @fun T u _ k l h => by
  wp_start as #Hinit
  wp_auto
  wp_apply wp_TypeKind k l h
  rw [internal.reflectlite.kind_w8 h]
  iapply HΦ
  itrivial

end proof

end Perennial
