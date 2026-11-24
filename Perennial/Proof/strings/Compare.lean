/-
The proof of `strings.Compare`.
-/
module

public import Perennial.Spec.strings.Compare
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
variable [package_sem : strings.Assumptions]

/-- Proved from the real Go, translated (`return bytealg.CompareString(a, b)`). -/
theorem strings.Compare.wp_proof
    (wp_CompareString : internal.bytealg.CompareString.spec (GF := GF) (hG := hG)) :
    strings.Compare.spec (GF := GF) (hG := hG) := by
  intro a b
  wp_start
  wp_auto
  wp_apply wp_CompareString
  rw [show internal.bytealg.compareResult a b = compareResult a b from rfl]
  iapply HΦ; itrivial

end proof

end Perennial
