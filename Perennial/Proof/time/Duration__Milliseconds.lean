/-
The proof of `time.Duration.Milliseconds`.
-/
module

public import Perennial.Spec.time.Duration__Milliseconds

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

theorem time.Duration.Milliseconds.wp_proof :
    time.Duration.Milliseconds.spec (GF := GF) (hG := hG) := by
  intro d
  wp_start
  repeat' (first | wp_if_destruct | wp_auto)
  all_goals wp_end

end proof

end Perennial
