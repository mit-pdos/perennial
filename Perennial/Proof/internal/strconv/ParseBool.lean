/-
The proof of `internal.strconv.ParseBool`.
-/
module

public import Perennial.Spec.internal.strconv.ParseBool

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

theorem internal.strconv.ParseBool.wp_proof :
    internal.strconv.ParseBool.spec (GF := GF) (hG := hG) := by
  intro str
  wp_start
  wp_auto
  repeat' (first | wp_if_destruct | wp_auto)
  all_goals (iapply HΦ; ipureintro; simp_all [internal.strconv.parseBool]; try rfl)

end proof

end Perennial
