/-
The proof of `internal.strconv.lower`.
-/
module

public import Perennial.Spec.internal.strconv.lower

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

theorem internal.strconv.lower.wp_proof :
    internal.strconv.lower.spec (GF := GF) (hG := hG) := by
  intro c
  wp_start
  wp_auto
  iapply HΦ; itrivial

end proof

end Perennial
