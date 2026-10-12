/-
The proof of `internal.bytealg.abigen_runtime_cmpstring`.
-/
module

public import Perennial.Spec.internal.bytealg.abigen_runtime_cmpstring

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

/-- Proved from the model of `abigen_runtime_cmpstring`
(`Perennial/TrustedCode/internal/bytealg.lean`). -/
theorem internal.bytealg.abigen_runtime_cmpstring.wp_proof :
    internal.bytealg.abigen_runtime_cmpstring.spec (GF := GF) (hG := hG) := fun a b => by
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
