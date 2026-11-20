/-
The proof of `time.Unix`.
-/
module

public import Perennial.Spec.time.Unix
public import Perennial.Spec.time.unixTime

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

theorem time.Unix.wp_proof
    (wp_unixTime : time.unixTime.spec (GF := GF) (hG := hG)) :
    time.Unix.spec (GF := GF) (hG := hG) := by
  intro sec nsec
  wp_start as #Hpkg
  repeat' (first | wp_if_destruct | wp_auto)
  all_goals (wp_apply wp_unixTime as %t -; wp_end)

end proof

end Perennial
