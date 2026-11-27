/-
The proof of `math.Floor` (`archFloor` on amd64).
-/
module

public import Perennial.Spec.math.Floor
public import Perennial.Spec.math.archFloor

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

theorem math.Floor.wp_proof
    (wp_archFloor : math.archFloor.spec (GF := GF) (hG := hG)) :
    math.Floor.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  wp_auto
  wp_apply wp_archFloor as %_ -
  (try wp_auto)
  wp_end

end proof

end Perennial
