/-
The proof of `reflect.rtype.Elem`.
-/
module

public import Perennial.Spec.reflect.rtype__Elem
public import Perennial.Spec.reflect.elem
public import Perennial.Spec.reflect.toType

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

theorem reflect.rtype.Elem.wp_proof
    (wp_elem : reflect.elem.spec (GF := GF) (hG := hG))
    (wp_toType : reflect.toType.spec (GF := GF) (hG := hG)) :
    reflect.rtype.Elem.spec (GF := GF) (hG := hG) := fun e l h => by
  wp_start as #Hinit
  wp_auto
  done

end proof

end Perennial
