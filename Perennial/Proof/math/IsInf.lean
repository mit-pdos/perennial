/-
The proof of `math.IsInf`.
-/
module

public import Perennial.Spec.math.IsInf
public import Perennial.Spec.math.Abs
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

theorem math.IsInf.wp_proof
    (wp_Abs : math.Abs.spec (GF := GF) (hG := hG)) :
    math.IsInf.spec (GF := GF) (hG := hG) := by
  intro f sign
  wp_start
  wp_auto
  wp_if_destruct
  · wp_apply wp_Abs
    (try wp_auto)
    wp_end
  wp_if_destruct
  · wp_apply wp_float64_neg as %_ -
    (try wp_auto)
    wp_end
  wp_end

end proof

end Perennial
