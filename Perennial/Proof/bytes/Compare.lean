/-
The proof of `bytes.Compare`.
-/
module

public import Perennial.Spec.bytes.Compare

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : bytes.Assumptions]

theorem bytes.Compare.wp_proof :
    bytes.Compare.spec (GF := GF) (hG := hG) := by
  intro sl_a sl_b da db a b
  wp_start
  iNamed Hpre
  wp_apply wp_bytes_to_string $$ Ha with Ha
  wp_apply wp_bytes_to_string $$ Hb with Hb
  unfold bytes.compareResult
  by_cases hlt : go.GoStringLt a b
  · simp only [hlt, decide_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    iframe
  · simp only [hlt, decide_false, ↓reduceIte]
    wp_auto
    by_cases heq : a = b
    · simp only [heq, decide_true, ↓reduceIte]
      wp_auto
      iapply HΦ
      iframe
    · simp only [heq, decide_false, ↓reduceIte]
      wp_auto
      iapply HΦ
      iframe

end proof

end Perennial
