/-
The proof of `unicode/utf8.ValidRune`.
-/
module

public import Perennial.Spec.unicode.utf8.ValidRune

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

theorem unicode.utf8.ValidRune.wp_proof : unicode.utf8.ValidRune.spec (GF := GF) (hG := hG) := by
  intro r
  wp_start
  wp_auto
  repeat' (first | wp_if_destruct | wp_auto)
  all_goals (iapply HΦ; ipureintro)
  all_goals (simp_all <;> word)

end proof

end Perennial
