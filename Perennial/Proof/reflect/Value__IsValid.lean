/-
The proof of `reflect.Value.IsValid`.
-/
module

public import Perennial.Spec.reflect.Value__IsValid

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

theorem reflect.Value.IsValid.wp_proof :
    reflect.Value.IsValid.spec (GF := GF) (hG := hG) := fun v => by
  wp_start
  wp_auto
  done

end proof

end Perennial
