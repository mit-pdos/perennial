/-
The proof of `math/rand.Rand.Int63`.
-/
module

public import Perennial.Spec.math.rand.Rand__Int63
public import Perennial.Spec.math.rand.runtimeSource__Int63

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

theorem math.rand.Rand.Int63.wp_proof
    (wp_runtimeSource_Int63 : math.rand.runtimeSource.Int63.spec (GF := GF) (hG := hG)) :
    math.rand.Rand.Int63.spec (GF := GF) (hG := hG) := by
  intro r
  wp_start as #Hr
  iunfold math.rand.isRuntimeRand at Hr
  icases Hr with ⟨%v, #Hr, %Hsrc⟩
  obtain ⟨⟨p, Hp⟩, -⟩ := Hsrc
  wp_auto
  iStructNamed Hr
  wp_auto
  simp only [Hp, interface.mkOk]
  wp_apply wp_runtimeSource_Int63 as %x %Hx
  iapply HΦ
  ipureintro; exact Hx

end proof

end Perennial
