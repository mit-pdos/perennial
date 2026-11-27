/-
The proof of `time.runtimeNano`.
-/
module

public import Perennial.Spec.time.runtimeNano
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

theorem time.runtimeNano.wp_proof
    (wp_now : time.now.spec (GF := GF) (hG := hG)) :
    time.runtimeNano.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply wp_now as %sec %nsec %mono -
  wp_if_destruct
  all_goals wp_end
  all_goals (ipureintro; word)

end proof

end Perennial
