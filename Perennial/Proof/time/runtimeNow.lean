/-
The proof of `time.runtimeNow`.
-/
module

public import Perennial.Spec.time.runtimeNow
public import Perennial.Spec.time.now_

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

theorem time.runtimeNow.wp_proof
    (wp_now : time.now.spec (GF := GF) (hG := hG)) :
    time.runtimeNow.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply wp_now as %sec %nsec %mono -
  wp_end

end proof

end Perennial
