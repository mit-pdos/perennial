/-
The proof of `internal.strconv.FormatBool`.
-/
module

public import Perennial.Spec.internal.strconv.FormatBool

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.strconv.Assumptions]

theorem internal.strconv.FormatBool.wp_proof :
    internal.strconv.FormatBool.spec (GF := GF) (hG := hG) := by
  intro b
  wp_start
  wp_auto
  cases b <;> (wp_auto; simp only [Bool.false_eq_true, ↓reduceIte]; iapply HΦ; itrivial)

end proof

end Perennial
