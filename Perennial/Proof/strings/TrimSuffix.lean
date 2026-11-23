/-
The proof of `strings.TrimSuffix`.
-/
module

public import Perennial.Spec.strings.TrimSuffix
public import Perennial.Spec.internal.stringslite.TrimSuffix

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

theorem strings.TrimSuffix.wp_proof
    (wp_TrimSuffix : internal.stringslite.TrimSuffix.spec (GF := GF) (hG := hG)) :
    strings.TrimSuffix.spec (GF := GF) (hG := hG) := by
  intro s suf
  wp_start
  wp_auto
  wp_apply wp_TrimSuffix
  iapply HΦ; itrivial

end proof

end Perennial
