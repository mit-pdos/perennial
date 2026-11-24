/-
The proof of `internal.bytealg.CompareString`.
-/
module

public import Perennial.Spec.internal.bytealg.CompareString

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

/-- Proved from the Go model of `CompareString`
(`goose/model/overlay/internal/bytealg/compare_native.go`), translated. -/
theorem internal.bytealg.CompareString.wp_proof :
    internal.bytealg.CompareString.spec (GF := GF) (hG := hG) := by
  intro a b
  wp_start
  wp_auto
  unfold internal.bytealg.compareResult
  by_cases hlt : go.GoStringLt a b
  · simp only [hlt, _root_.decide_true, ↓reduceIte]
    wp_auto
    iapply HΦ; itrivial
  · simp only [hlt, _root_.decide_false, ↓reduceIte]
    wp_auto
    by_cases heq : a = b
    · simp only [heq, _root_.decide_true, ↓reduceIte]
      wp_auto
      iapply HΦ; itrivial
    · simp only [heq, _root_.decide_false, ↓reduceIte]
      wp_auto
      iapply HΦ; itrivial

end proof

end Perennial
