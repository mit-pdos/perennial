/-
The proof of `strings.Compare`.
-/
module

public import Perennial.Spec.strings.Compare
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

/-- Proved from the model of `Compare` (`Perennial/TrustedCode/strings.lean`). -/
theorem strings.Compare.wp_proof :
    strings.Compare.spec (GF := GF) (hG := hG) := by
  intro a b
  wp_start
  unfold compareResult
  by_cases hlt : go.GoStringLt a b
  · simp only [hlt, decide_true, ↓reduceIte]
    wp_auto
    iapply HΦ; itrivial
  · simp only [hlt, decide_false, ↓reduceIte]
    wp_auto
    by_cases heq : a = b
    · simp only [heq, decide_true, ↓reduceIte]
      wp_auto
      iapply HΦ; itrivial
    · simp only [heq, decide_false, ↓reduceIte]
      wp_auto
      iapply HΦ; itrivial

end proof

end Perennial
