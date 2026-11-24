/-
The proof of `reflect.isModelRType`.
-/
module

public import Perennial.Spec.reflect.isModelRType
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

theorem reflect.isModelRType.wp_proof
    (wp_TokOf : internal.reflectcore.TokOf.spec (GF := GF) (hG := hG)) :
    reflect.isModelRType.spec (GF := GF) (hG := hG) := fun T l hT => by
  wp_start as #Hinit
  wp_auto
  wp_apply wp_TokOf
  rw [ite_eq_right (by simpa using hT)]
  wp_auto
  iapply HΦ
  itrivial

end proof

end Perennial
