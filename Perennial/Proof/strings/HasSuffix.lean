/-
The proof of `strings.HasSuffix`.
-/
module

public import Perennial.Spec.strings.HasSuffix
public import Perennial.Spec.internal.stringslite.HasSuffix

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

theorem strings.HasSuffix.wp_proof
    (wp_HasSuffix : internal.stringslite.HasSuffix.spec (GF := GF) (hG := hG)) :
    strings.HasSuffix.spec (GF := GF) (hG := hG) := by
  intro s suf
  wp_start
  wp_auto
  wp_apply wp_HasSuffix
  iapply HΦ; itrivial

end proof

end Perennial
