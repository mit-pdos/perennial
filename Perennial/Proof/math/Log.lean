/-
The proof of `math.Log` (`archLog` on amd64).
-/
module

public import Perennial.Spec.math.Log
public import Perennial.Spec.math.archLog

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.Assumptions]

theorem math.Log.wp_proof
    (wp_archLog : math.archLog.spec (GF := GF) (hG := hG)) :
    math.Log.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  wp_auto
  wp_apply wp_archLog as %_ -
  (try wp_auto)
  wp_end

end proof

end Perennial
