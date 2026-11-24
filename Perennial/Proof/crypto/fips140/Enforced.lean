/-
The proof of `crypto/fips140.Enforced`.
-/
module

public import Perennial.Spec.crypto.fips140.Enforced

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.fips140.Assumptions]

/-- `isBypassed` is the trusted model (an arbitrary `bool`), reached only when `enabled`. -/
theorem crypto.fips140.Enforced.wp_proof : crypto.fips140.Enforced.spec (GF := GF) (hG := hG) := by
  wp_start
  icases crypto.fips140.isInit_access $$ Hpkg with ⟨%b, #He, %Hb⟩
  wp_auto
  cases b
  · wp_auto
    wp_end
  · wp_auto
    wp_func_call
    wp_call
    wp_apply wp_ArbitraryInt as %x -
    iapply HΦ
    ipureintro
    intro _
    exact Hb rfl

end proof

end Perennial
