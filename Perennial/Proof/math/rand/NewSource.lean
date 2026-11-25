/-
The proof of `math/rand.NewSource`.
-/
module

public import Perennial.Spec.math.rand.NewSource
public import Perennial.Spec.math.rand.newSource_

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

theorem math.rand.NewSource.wp_proof
    (wp_newSource : math.rand.newSource.spec (GF := GF) (hG := hG)) :
    math.rand.NewSource.spec (GF := GF) (hG := hG) := by
  intro seed
  wp_start as #Hpkg
  wp_auto
  wp_apply wp_newSource $$ Hpkg as %p Hp
  iapply HΦ
  iexists p
  iframe Hp
  ipureintro; rfl

end proof

end Perennial
