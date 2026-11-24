/-
The proof of `reflect.elem`.
-/
module

public import Perennial.Spec.reflect.elem
public import Perennial.Spec.internal.reflectcore.TypeKind
public import Perennial.Spec.internal.reflectcore.TypeElem

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

theorem reflect.elem.wp_proof
    (wp_TypeKind : internal.reflectcore.TypeKind.spec (GF := GF) (hG := hG))
    (wp_TypeElem : internal.reflectcore.TypeElem.spec (GF := GF) (hG := hG)) :
    reflect.elem.spec (GF := GF) (hG := hG) := fun e l h => by
  wp_start as #Hinit
  wp_auto
  done

end proof

end Perennial
