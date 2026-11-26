/-
The proof of `math/rand.New`.
-/
module

public import Perennial.Spec.math.rand.New

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

theorem math.rand.New.wp_proof : math.rand.New.spec (GF := GF) (hG := hG) := by
  intro src
  wp_start
  iapply wp_fupd
  wp_auto
  cases src
  case nil => wp_auto; (ipersist «$r0»; imodintro; iapply HΦ; iexists _; iframe «$r0»; ipureintro; rfl)
  case ok ii =>
    by_cases h : go.typeSetContains ii.ty Source64.ty = true <;> simp only [h, ↓reduceIte] <;>
      wp_auto <;>
      (ipersist «$r0»; imodintro; iapply HΦ; iexists _; iframe «$r0»; ipureintro; rfl)

end proof

end Perennial
