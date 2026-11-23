/-
The proof of `crypto/internal/boring.Unreachable`.
-/
module

public import Perennial.Spec.crypto.internal.boring.Unreachable
public import Perennial.Spec.crypto.internal.boring.sig.StandardCrypto

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.internal.boring.Assumptions]

theorem crypto.internal.boring.Unreachable.wp_proof
    (wp_StandardCrypto : crypto.internal.boring.sig.StandardCrypto.spec (GF := GF) (hG := hG)) :
    crypto.internal.boring.Unreachable.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_apply wp_StandardCrypto
  wp_end

end proof

end Perennial
