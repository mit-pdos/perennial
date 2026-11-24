/-
The proof of `strconv.AppendQuote`.
-/
module

public import Perennial.Spec.strconv.AppendQuote
public import Perennial.Spec.strconv.appendQuotedWith

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strconv.Assumptions]

theorem strconv.AppendQuote.wp_proof
    (wp_appendQuotedWith : strconv.appendQuotedWith.spec (GF := GF) (hG := hG)) :
    strconv.AppendQuote.spec (GF := GF) (hG := hG) := by
  intro dst bs s Hs
  wp_start as ⟨Hd, Hcap⟩
  wp_auto
  wp_apply wp_appendQuotedWith _ _ _ _ _ Hs $$ [$Hd $Hcap] as %d' Hd'
  iapply HΦ $$ Hd'

end proof

end Perennial
