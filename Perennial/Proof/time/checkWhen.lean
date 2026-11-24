/-
The proof of `time.checkWhen`.
-/
module

public import Perennial.Spec.time.checkWhen

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

theorem time.checkWhen.wp_proof : time.checkWhen.spec (GF := GF) (hG := hG) := by
  intro w p
  wp_start as %H
  wp_auto
  repeat' (first | (exfalso; word; done) | wp_if_destruct)
  all_goals wp_end

end proof

end Perennial
