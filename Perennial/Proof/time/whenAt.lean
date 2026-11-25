/-
The proof of `time.whenAt`.
-/
module

public import Perennial.Spec.time.whenAt

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

theorem time.whenAt.wp_proof : time.whenAt.spec (GF := GF) (hG := hG) := by
  intro now d
  wp_start
  wp_auto
  repeat' wp_if_destruct
  all_goals wp_end
  all_goals ipureintro
  · exact Or.inl ⟨by word, rfl⟩
  all_goals first
    | exact Or.inr (Or.inl ⟨by word, by word, rfl⟩)
    | exact Or.inr (Or.inr ⟨by word, by word, rfl⟩)

end proof

end Perennial
