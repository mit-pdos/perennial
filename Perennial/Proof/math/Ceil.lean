/-
The proof of `math.Ceil` (`archCeil` on amd64).
-/
module

public import Perennial.Spec.math.Ceil
public import Perennial.Spec.math.archCeil

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

theorem math.Ceil.wp_proof
    (wp_archCeil : math.archCeil.spec (GF := GF) (hG := hG)) :
    math.Ceil.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  wp_auto
  wp_apply wp_archCeil as %_ -
  (try wp_auto)
  wp_end

end proof

end Perennial
