/-
The proof of `math.floor`.
-/
module

public import Perennial.Spec.math.floor_
public import Perennial.Spec.math.IsNaN
public import Perennial.Spec.math.IsInf
public import Perennial.Spec.math.Modf
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

theorem math.floor.wp_proof
    (wp_IsNaN : math.IsNaN.spec (GF := GF) (hG := hG))
    (wp_IsInf : math.IsInf.spec (GF := GF) (hG := hG))
    (wp_Modf : math.Modf.spec (GF := GF) (hG := hG)) :
    math.floor.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  (try wp_auto)
  repeat' (first
    | wp_end
    | (wp_apply wp_IsNaN; (try wp_auto))
    | (wp_apply wp_IsInf as %_ -; (try wp_auto))
    | (wp_apply wp_Modf as %_ %_ -; (try wp_auto))
    | (wp_apply wp_float64_add as %_ -; (try wp_auto))
    | (wp_apply wp_float64_neg as %_ -; (try wp_auto))
    | wp_auto
    | wp_if_destruct
    | (wp_if_bool; wp_if_destruct))

end proof

end Perennial
