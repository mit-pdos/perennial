/-
The proof of `strings.Index`.
-/
module

public import Perennial.Spec.strings.Index
public import Perennial.Spec.internal.stringslite.Index
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

theorem strings.Index.wp_proof
    (wp_stringslite_Index : internal.stringslite.Index.spec (GF := GF) (hG := hG)) :
    strings.Index.spec (GF := GF) (hG := hG) := by
  intro s substr
  wp_start as #Hinit
  wp_auto
  wp_apply wp_stringslite_Index as %H
  iapply HΦ
  ipureintro
  exact H

end proof

end Perennial
