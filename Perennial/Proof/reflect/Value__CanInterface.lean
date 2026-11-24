/-
The proof of `reflect.Value.CanInterface`.
-/
module

public import Perennial.Spec.reflect.Value__CanInterface

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

theorem reflect.Value.CanInterface.wp_proof :
    reflect.Value.CanInterface.spec (GF := GF) (hG := hG) := fun v hv => by
  wp_start
  wp_auto
  done

end proof

end Perennial
