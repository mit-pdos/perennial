/-
The proof of `math.Modf`.
-/
module

public import Perennial.Spec.math.Modf
public import Perennial.Spec.math.Trunc
public import Perennial.Spec.math.Copysign
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

theorem math.Modf.wp_proof
    (wp_Trunc : math.Trunc.spec (GF := GF) (hG := hG))
    (wp_Copysign : math.Copysign.spec (GF := GF) (hG := hG)) :
    math.Modf.spec (GF := GF) (hG := hG) := by
  intro f
  wp_start
  wp_auto
  wp_apply wp_Trunc as %_ -
  (try wp_auto)
  wp_apply wp_float64_sub as %_ -
  (try wp_auto)
  wp_apply wp_Copysign as %_ -
  (try wp_auto)
  wp_end

end proof

end Perennial
