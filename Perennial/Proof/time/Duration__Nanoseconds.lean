/-
The proof of `time.Duration.Nanoseconds`.
-/
module

public import Perennial.Spec.time.Duration__Nanoseconds

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

theorem time.Duration.Nanoseconds.wp_proof :
    time.Duration.Nanoseconds.spec (GF := GF) (hG := hG) := by
  intro d
  wp_start
  repeat' (first | wp_if_destruct | wp_auto)
  all_goals wp_end

end proof

end Perennial
