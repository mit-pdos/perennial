/-
The proof of `time.Time.UTC`.
-/
module

public import Perennial.Spec.time.Time__UTC
public import Perennial.Spec.time.Time__setLoc

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

theorem time.Time.UTC.wp_proof
    (wp_Time_setLoc : time.Time.setLoc.spec (GF := GF) (hG := hG)) :
    time.Time.UTC.spec (GF := GF) (hG := hG) := by
  intro t
  wp_start
  wp_auto
  wp_apply wp_Time_setLoc $$ [$t] as %tv' t
  (try wp_auto)
  wp_end

end proof

end Perennial
