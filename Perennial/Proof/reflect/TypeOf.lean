/-
The proof of `reflect.TypeOf`.
-/
module

public import Perennial.Spec.reflect.TypeOf
public import Perennial.Spec.reflect.isModelRType
public import Perennial.Spec.reflect.toRType
public import Perennial.Spec.internal.reflectcore.TokOf

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

theorem reflect.TypeOf.wp_proof
    (wp_TokOf : internal.reflectcore.TokOf.spec (GF := GF) (hG := hG))
    (wp_isModelRType : reflect.isModelRType.spec (GF := GF) (hG := hG))
    (wp_toRType : reflect.toRType.spec (GF := GF) (hG := hG)) :
    reflect.TypeOf.spec (GF := GF) (hG := hG) := by
  constructor
  · intro t v ht
    wp_start as #Hinit
    wp_auto
    wp_apply wp_TokOf
    unfold go.tok
    wp_apply wp_isModelRType t null ht
    wp_apply wp_toRType
    iapply HΦ
    itrivial
  · wp_start as #Hinit
    wp_auto
    iapply HΦ
    itrivial

end proof

end Perennial
