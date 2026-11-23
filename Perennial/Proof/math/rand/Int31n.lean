/-
The proof of `math/rand.Int31n`.
-/
module

public import Perennial.Spec.math.rand.Int31n
public import Perennial.Spec.math.rand.Rand__Int31n
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

theorem math.rand.Int31n.wp_proof
    (wp_globalRand : math.rand.globalRand.spec (GF := GF) (hG := hG))
    (wp_Rand_Int31n : math.rand.Rand.Int31n.spec (GF := GF) (hG := hG)) :
    math.rand.Int31n.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start as %Hn
  wp_auto
  wp_apply wp_globalRand $$ Hpkg as %r #Hr
  wp_apply wp_Rand_Int31n $$ [Hr] as %x %Hx
  · iframe Hr; ipureintro; exact Hn
  try wp_auto
  iapply HΦ; ipureintro; exact Hx

end proof

end Perennial
