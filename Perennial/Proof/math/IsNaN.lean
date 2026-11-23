/-
The proof of `math.IsNaN`.
-/
module

public import Perennial.Spec.math.IsNaN
public import Perennial.Golang.Theory.Float

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

theorem math.IsNaN.wp_proof :
    math.IsNaN.spec (GF := GF) (hG := hG) := by
  intro f
  wp_start
  wp_auto
  simp only [float64Eq_self, Bool.not_not]
  wp_end

end proof

end Perennial
