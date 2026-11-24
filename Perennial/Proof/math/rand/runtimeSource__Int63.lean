/-
The proof of `math/rand.runtimeSource.Int63`.
-/
module

public import Perennial.Spec.math.rand.runtimeSource__Int63
public import Perennial.Spec.math.rand.runtime_rand

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

theorem math.rand.runtimeSource.Int63.wp_proof
    (wp_runtime_rand : math.rand.runtime_rand.spec (GF := GF) (hG := hG)) :
    math.rand.runtimeSource.Int63.spec (GF := GF) (hG := hG) := by
  intro p
  wp_start
  wp_auto
  wp_apply wp_runtime_rand as %y -
  iapply HΦ
  ipureintro
  exact (math.rand.and_toInt_bounds y _ (by decide)).1

end proof

end Perennial
