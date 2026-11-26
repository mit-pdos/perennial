/-
The proof of `math.ldexp`.
-/
module

public import Perennial.Spec.math.ldexp_
public import Perennial.Spec.math.IsInf
public import Perennial.Spec.math.IsNaN
public import Perennial.Spec.math.normalize
public import Perennial.Spec.math.Float64bits
public import Perennial.Spec.math.Float64frombits
public import Perennial.Spec.math.Copysign
public import Perennial.Spec.math.Inf
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

set_option maxHeartbeats 2000000 in
theorem math.ldexp.wp_proof
    (wp_IsInf : math.IsInf.spec (GF := GF) (hG := hG))
    (wp_IsNaN : math.IsNaN.spec (GF := GF) (hG := hG))
    (wp_normalize : math.normalize.spec (GF := GF) (hG := hG))
    (wp_Float64bits : math.Float64bits.spec (GF := GF) (hG := hG))
    (wp_Float64frombits : math.Float64frombits.spec (GF := GF) (hG := hG))
    (wp_Copysign : math.Copysign.spec (GF := GF) (hG := hG))
    (wp_Inf : math.Inf.spec (GF := GF) (hG := hG)) :
    math.ldexp.spec (GF := GF) (hG := hG) := by
  intro frac exp
  wp_start
  (try wp_auto)
  repeat' (first
    | wp_end
    | (wp_apply wp_IsInf as %_ -; (try wp_auto))
    | (wp_apply wp_IsNaN; (try wp_auto))
    | (wp_apply wp_normalize as %_ %_ -; (try wp_auto))
    | (wp_apply wp_Float64bits; (try wp_auto))
    | (wp_apply wp_Float64frombits; (try wp_auto))
    | (wp_apply wp_Copysign as %_ -; (try wp_auto))
    | (wp_apply wp_Inf as %_ -; (try wp_auto))
    | (wp_apply wp_float64_mul as %_ -; (try wp_auto))
    | wp_auto
    | wp_if_destruct
    | (wp_if_bool; wp_if_destruct))

end proof

end Perennial
