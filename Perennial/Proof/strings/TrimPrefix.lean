/-
The proof of `strings.TrimPrefix`.
-/
module

public import Perennial.Spec.strings.TrimPrefix
public import Perennial.Spec.internal.stringslite.TrimPrefix

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

theorem strings.TrimPrefix.wp_proof
    (wp_TrimPrefix : internal.stringslite.TrimPrefix.spec (GF := GF) (hG := hG)) :
    strings.TrimPrefix.spec (GF := GF) (hG := hG) := by
  intro s pfx
  wp_start
  wp_auto
  wp_apply wp_TrimPrefix
  unfold trimPrefix
  iapply HΦ; itrivial

end proof

end Perennial
