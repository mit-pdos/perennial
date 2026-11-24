/-
The proof of `reflect.toType`.
-/
module

public import Perennial.Spec.reflect.toType
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

theorem reflect.toType.wp_proof
    (wp_toRType : reflect.toRType.spec (GF := GF) (hG := hG)) :
    reflect.toType.spec (GF := GF) (hG := hG) := fun t => by
  cases t with
  | nil =>
    simp only [↓reduceIte]
    wp_start as #Hinit
    wp_auto
    iapply HΦ
    itrivial
  | ok i =>
    simp only [reduceCtorEq, ↓reduceIte]
    wp_start as #Hinit
    wp_auto
    wp_apply wp_toRType
    iapply HΦ
    itrivial

end proof

end Perennial
