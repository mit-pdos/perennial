/-
The proof of `math/rand.Rand.Int31`.
-/
module

public import Perennial.Spec.math.rand.Rand__Int31
public import Perennial.Spec.math.rand.Rand__Int63

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

theorem math.rand.Rand.Int31.wp_proof
    (wp_Int63 : math.rand.Rand.Int63.spec (GF := GF) (hG := hG)) :
    math.rand.Rand.Int31.spec (GF := GF) (hG := hG) := by
  intro r
  wp_start as #Hr
  wp_auto
  wp_apply wp_Int63 $$ Hr as %x %Hx
  iapply HΦ
  ipureintro; exact math.rand.int31_nonneg_of_int63 x Hx

end proof

end Perennial
