/-
The proof of `reflect.rtype.Kind`.
-/
module

public import Perennial.Spec.reflect.rtype__Kind
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
variable [package_sem : reflect.Assumptions]

theorem reflect.rtype.Kind.wp_proof
    (wp_TypeKind : internal.reflectcore.TypeKind.spec (GF := GF) (hG := hG)) :
    reflect.rtype.Kind.spec (GF := GF) (hG := hG) := @fun T u _ _ k l h => by
  wp_start as #Hinit
  wp_auto
  wp_apply wp_TypeKind k l h
  iapply HΦ
  itrivial

end proof

end Perennial
