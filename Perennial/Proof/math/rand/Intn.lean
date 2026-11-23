/-
The proof of `math/rand.Intn`.
-/
module

public import Perennial.Spec.math.rand.Intn
public import Perennial.Spec.math.rand.Rand__Intn
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

theorem math.rand.Intn.wp_proof
    (wp_globalRand : math.rand.globalRand.spec (GF := GF) (hG := hG))
    (wp_Rand_Intn : math.rand.Rand.Intn.spec (GF := GF) (hG := hG)) :
    math.rand.Intn.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start as %Hn
  wp_auto
  wp_apply wp_globalRand $$ Hpkg as %r #Hr
  wp_apply wp_Rand_Intn $$ [Hr] as %x %Hx
  · iframe Hr; ipureintro; exact Hn
  try wp_auto
  iapply HΦ; ipureintro; exact Hx

end proof

end Perennial
