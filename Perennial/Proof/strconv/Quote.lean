/-
The proof of `strconv.Quote`.
-/
module

public import Perennial.Spec.strconv.Quote
public import Perennial.Spec.strconv.quoteWith

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

theorem strconv.Quote.wp_proof
    (wp_quoteWith : strconv.quoteWith.spec (GF := GF) (hG := hG)) :
    strconv.Quote.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start
  wp_auto
  wp_apply wp_quoteWith _ _ _ as %q -
  iapply HΦ
  itrivial

end proof

end Perennial
