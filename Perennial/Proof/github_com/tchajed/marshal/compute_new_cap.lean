/-
The proof of `github.com/tchajed/marshal.compute_new_cap`.
-/
module

public import Perennial.Spec.github_com.tchajed.marshal.compute_new_cap

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.tchajed.marshal.Assumptions]

theorem github_com.tchajed.marshal.compute_new_cap.wp_proof :
    github_com.tchajed.marshal.compute_new_cap.spec (GF := GF) (hG := hG) := fun old_cap min_cap => by
  wp_start
  wp_auto
  wp_if_destruct
  · iapply HΦ; ipureintro; exact ⟨by omega, .inl rfl⟩
  · iapply HΦ; ipureintro; exact ⟨by simp only [uint.Z] at *; omega, .inr rfl⟩

end proof

end Perennial
