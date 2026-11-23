/-
The proof of `time.Duration.Abs`.
-/
module

public import Perennial.Spec.time.Duration__Abs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

theorem time.Duration.Abs.wp_proof :
    time.Duration.Abs.spec (GF := GF) (hG := hG) := by
  intro d
  wp_start
  wp_auto
  wp_if_destruct
  · rw [if_pos (by simpa using Hif)]
    wp_end
  · have Hge := Hif
    wp_if_destruct
    · simp only [time.maxDuration]
      wp_auto
      rw [if_neg (by simpa using Hge), if_pos (by simpa using Hif)]
      wp_end
    · rw [if_neg (by simpa using Hge), if_neg (by simpa using Hif)]
      wp_end

end proof

end Perennial
