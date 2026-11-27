/-
The proof of `math.isOddInt`.
-/
module

public import Perennial.Spec.math.isOddInt
public import Perennial.Spec.math.Abs
public import Perennial.Spec.math.Modf

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

theorem math.isOddInt.wp_proof
    (wp_Abs : math.Abs.spec (GF := GF) (hG := hG))
    (wp_Modf : math.Modf.spec (GF := GF) (hG := hG)) :
    math.isOddInt.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  (try wp_auto)
  repeat' (first
    | wp_end
    | (wp_apply wp_Abs; (try wp_auto))
    | (wp_apply wp_Modf as %_ %_ -; (try wp_auto))
    | (wp_apply wp_ArbitraryInt as %_ -; (try wp_auto))
    | wp_auto
    | wp_if_destruct
    | (wp_if_bool; wp_if_destruct))

end proof

end Perennial
