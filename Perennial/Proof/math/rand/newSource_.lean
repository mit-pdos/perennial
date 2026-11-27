/-
The proof of `math/rand.newSource`.
-/
module

public import Perennial.Spec.math.rand.newSource_
public import Perennial.Spec.math.rand.rngSource__Seed

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

theorem math.rand.newSource.wp_proof
    (wp_Seed : math.rand.rngSource.Seed.spec (GF := GF) (hG := hG)) :
    math.rand.newSource.spec (GF := GF) (hG := hG) := by
  intro seed
  wp_start as #Hpkg
  wp_auto
  wp_apply wp_Seed $$ [Hpkg rng] as Hp
  · iframe
  try wp_auto
  iapply HΦ
  iexact Hp

end proof

end Perennial
