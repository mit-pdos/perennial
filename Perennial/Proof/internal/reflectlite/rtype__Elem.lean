/-
The proof of `internal.reflectlite.rtype.Elem`.
-/
module

public import Perennial.Spec.internal.reflectlite.rtype__Elem
public import Perennial.Spec.internal.reflectlite.elem
public import Perennial.Spec.internal.reflectlite.toType

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

theorem internal.reflectlite.rtype.Elem.wp_proof
    (wp_elem : internal.reflectlite.elem.spec (GF := GF) (hG := hG))
    (wp_toType : internal.reflectlite.toType.spec (GF := GF) (hG := hG)) :
    internal.reflectlite.rtype.Elem.spec (GF := GF) (hG := hG) := @fun T u hu e l h => by
  wp_start as #Hinit
  wp_auto
  wp_apply wp_elem e l h
  wp_apply wp_toType
  simp only [go.tok, reduceCtorEq, ↓reduceIte]
  iapply HΦ
  itrivial

end proof

end Perennial
