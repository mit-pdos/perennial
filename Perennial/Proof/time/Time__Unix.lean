/-
The proof of `time.Time.Unix`.
-/
module

public import Perennial.Spec.time.Time__Unix
public import Perennial.Spec.time.Time__unixSec

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

theorem time.Time.Unix.wp_proof
    (wp_Time_unixSec : time.Time.unixSec.spec (GF := GF) (hG := hG)) :
    time.Time.Unix.spec (GF := GF) (hG := hG) := by
  intro t
  wp_start
  wp_auto
  wp_apply wp_Time_unixSec $$ [$t] as %x t
  wp_end

end proof

end Perennial
