/-
The proof of `math/rand.rngSource.Int63`.
-/
module

public import Perennial.Spec.math.rand.rngSource__Int63
public import Perennial.Spec.math.rand.rngSource__Uint64

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

theorem math.rand.rngSource.Int63.wp_proof
    (wp_Uint64 : math.rand.rngSource.Uint64.spec (GF := GF) (hG := hG)) :
    math.rand.rngSource.Int63.spec (GF := GF) (hG := hG) := by
  intro p
  wp_start as Hp
  wp_auto
  wp_apply wp_Uint64 $$ Hp as %y Hp
  iapply HΦ
  iframe Hp
  ipureintro
  exact (math.rand.and_toInt_bounds y _ (by decide)).1

end proof

end Perennial
