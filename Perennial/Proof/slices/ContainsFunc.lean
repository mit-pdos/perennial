/-
The proof of `slices.ContainsFunc`.
-/
module

public import Perennial.Spec.slices.ContainsFunc

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

theorem slices.ContainsFunc.wp_proof
    (wp_IndexFunc : slices.IndexFunc.spec (GF := GF) (hG := hG)) :
    slices.ContainsFunc.spec (GF := GF) (hG := hG) := by
  intro V _ _ Et _ S _ s dq xs f P
  wp_start as ⟨Hs, #Hf⟩
  wp_auto
  wp_apply wp_IndexFunc s dq xs f P $$ [Hs] as %i ⟨Hs, %Hi⟩
  · iframe; iframe #
  iapply HΦ
  iframe
  ipureintro
  rcases Hi with ⟨hi, hall⟩ | ⟨hi, x, hx, hP, -⟩
  · have : ¬ (sint.Z (W64 0) ≤ sint.Z i) := by word
    simp only [this, decide_false]
    exact hall
  · have : sint.Z (W64 0) ≤ sint.Z i := by word
    simp only [this, decide_true, ↓reduceIte]
    exact ⟨x, List.mem_of_getElem? hx, hP⟩

end proof

end Perennial
