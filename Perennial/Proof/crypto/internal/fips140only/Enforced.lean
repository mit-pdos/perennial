/-
The proof of `crypto/internal/fips140only.Enforced`.
-/
module

public import Perennial.Spec.crypto.internal.fips140only.Enforced
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
variable [package_sem : crypto.internal.fips140only.Assumptions]

theorem crypto.internal.fips140only.Enforced.wp_proof
    (wp_Enforced : crypto.fips140.Enforced.spec (GF := GF) (hG := hG)) :
    crypto.internal.fips140only.Enforced.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply wp_Enforced as %b %Hb
  wp_end

end proof

end Perennial
