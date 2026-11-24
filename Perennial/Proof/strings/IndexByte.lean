/-
The proof of `strings.IndexByte`.
-/
module

public import Perennial.Spec.strings.IndexByte
public import Perennial.Spec.internal.stringslite.IndexByte

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

theorem strings.IndexByte.wp_proof
    (wp_stringslite_IndexByte : internal.stringslite.IndexByte.spec (GF := GF) (hG := hG)) :
    strings.IndexByte.spec (GF := GF) (hG := hG) := by
  intro s c
  wp_start
  wp_auto
  wp_apply wp_stringslite_IndexByte as %-
  iapply HΦ
  itrivial

end proof

end Perennial
