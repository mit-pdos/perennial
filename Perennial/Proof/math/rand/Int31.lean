/-
The proof of `math/rand.Int31`.
-/
module

public import Perennial.Spec.math.rand.Int31
public import Perennial.Spec.math.rand.Rand__Int31
public import Perennial.Spec.math.rand.globalRand

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.rand.Assumptions]

theorem math.rand.Int31.wp_proof
    (wp_globalRand : math.rand.globalRand.spec (GF := GF) (hG := hG))
    (wp_Rand_Int31 : math.rand.Rand.Int31.spec (GF := GF) (hG := hG)) :
    math.rand.Int31.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply wp_globalRand $$ Hpkg as %r #Hr
  wp_apply wp_Rand_Int31 $$ Hr as %x %Hx
  try wp_auto
  iapply HΦ; ipureintro; exact Hx

end proof

end Perennial
