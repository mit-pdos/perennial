/-
The proof of `unicode.utf8.DecodeRuneInString`.
-/
module

public import Perennial.Spec.unicode.utf8.DecodeRuneInString

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : unicode.utf8.Assumptions]

theorem unicode.utf8.DecodeRuneInString.wp_proof :
    unicode.utf8.DecodeRuneInString.spec (GF := GF) (hG := hG) := fun c s Hc => by
  wp_start
  wp_auto
  wp_if_destruct
  · have Hr : W32 ((uint.nat c : Nat) : Int) = W32 (uint.Z c) := by word
    rw [Hr]
    iapply HΦ
    itrivial
  · exfalso; word

end proof

end Perennial
