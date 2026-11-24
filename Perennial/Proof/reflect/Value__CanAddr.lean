/-
The proof of `reflect.Value.CanAddr`.
-/
module

public import Perennial.Spec.reflect.Value__CanAddr

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

theorem reflect.Value.CanAddr.wp_proof :
    reflect.Value.CanAddr.spec (GF := GF) (hG := hG) := fun v => by
  simp only [ne_eq, decide_not]
  wp_start
  wp_auto
  iapply HΦ
  itrivial

end proof

end Perennial
