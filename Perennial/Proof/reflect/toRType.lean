/-
The proof of `reflect.toRType`.
-/
module

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

theorem reflect.toRType.wp_proof :
    reflect.toRType.spec (GF := GF) (hG := hG) := fun t => by
  wp_start
  wp_auto
  wp_end

end proof

end Perennial
