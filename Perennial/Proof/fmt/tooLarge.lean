/-
The proof of `fmt.tooLarge`.
-/
module

public import Perennial.Spec.fmt.tooLarge

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

theorem fmt.tooLarge.wp_proof : fmt.tooLarge.spec (GF := GF) (hG := hG) :=
    fun x => by
  wp_start
  wp_auto
  wp_if_destruct
  · rw [show decide (1000000 < sint.Z x ∨ sint.Z x < -1000000) = true from
      decide_eq_true (Or.inl (by word))]
    iapply HΦ
    ipureintro; trivial
  · rw [show decide (1000000 < sint.Z x ∨ sint.Z x < -1000000) =
        decide (sint.Z x < sint.Z (-W64 1000000)) from by
      simp only [decide_eq_decide]; constructor
      · rintro (h | h)
        · exfalso; apply Hif; word
        · word
      · intro h; right; word]
    iapply HΦ
    ipureintro; trivial

end proof

end Perennial
