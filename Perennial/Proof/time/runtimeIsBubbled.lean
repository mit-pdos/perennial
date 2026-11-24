/-
The proof of `time.runtimeIsBubbled`.
-/
module

public import Perennial.Spec.time.runtimeIsBubbled
public import Perennial.Spec.internal.gomodel.Choose

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

theorem time.runtimeIsBubbled.wp_proof
    (wp_Choose : internal.gomodel.Choose.spec (GF := GF) (hG := hG)) :
    time.runtimeIsBubbled.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply wp_Choose as %b -
  wp_end

end proof

end Perennial
