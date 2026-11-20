/-
The proof of `time.Time.IsZero`.
-/
module

public import Perennial.Spec.time.Time__IsZero

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

theorem time.Time.IsZero.wp_proof :
    time.Time.IsZero.spec (GF := GF) (hG := hG) := by
  intro t
  wp_start
  wp_auto
  by_cases hw : t.wall' = W64 0
  · simp only [hw, decide_true, true_and]
    wp_auto
    iapply HΦ; itrivial
  · simp only [hw, decide_false, false_and]
    wp_auto
    iapply HΦ; itrivial

end proof

end Perennial
