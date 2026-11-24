/-
The proof of `internal.stringslite.IndexByte`.
-/
module

public import Perennial.Spec.internal.stringslite.IndexByte
public import Perennial.Spec.internal.bytealg.IndexByteString

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.stringslite.Assumptions]

theorem internal.stringslite.IndexByte.wp_proof
    (wp_IndexByteString : internal.bytealg.IndexByteString.spec (GF := GF) (hG := hG)) :
    internal.stringslite.IndexByte.spec (GF := GF) (hG := hG) := by
  intro s c
  wp_start
  wp_auto
  wp_apply wp_IndexByteString as %Hl
  iapply HΦ
  ipureintro
  exact Hl

end proof

end Perennial
