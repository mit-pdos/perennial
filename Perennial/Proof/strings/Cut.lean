/-
The proof of `strings.Cut`.
-/
module

public import Perennial.Spec.strings.Cut
public import Perennial.Spec.internal.stringslite.Cut

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

theorem strings.Cut.wp_proof
    (wp_stringslite_Cut : internal.stringslite.Cut.spec (GF := GF) (hG := hG)) :
    strings.Cut.spec (GF := GF) (hG := hG) := by
  intro s sep
  wp_start as #Hinit
  wp_auto
  wp_apply wp_stringslite_Cut
  iapply HΦ
  itrivial

end proof

end Perennial
