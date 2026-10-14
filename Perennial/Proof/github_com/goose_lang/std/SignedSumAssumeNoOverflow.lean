/-
The proof of `github.com/goose-lang/std.SignedSumAssumeNoOverflow`.
-/
module

public import Perennial.Spec.github_com.goose_lang.std.SignedSumAssumeNoOverflow
public import Perennial.Spec.github_com.goose_lang.primitive.Assume

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.goose_lang.std.Assumptions]

theorem github_com.goose_lang.std.SignedSumAssumeNoOverflow.wp_proof
    (wp_Assume : github_com.goose_lang.primitive.Assume.spec (GF := GF) (hG := hG)) :
    github_com.goose_lang.std.SignedSumAssumeNoOverflow.spec (GF := GF) (hG := hG) := fun x y => by
  wp_start
  wp_auto
  simp only [math.MaxInt, math.MinInt]
  wp_if_destruct
  · wp_if_destruct
    · wp_apply wp_Assume as %_
      iapply HΦ; ipureintro; word
    · wp_if_destruct
      · wp_if_destruct
        · wp_apply wp_Assume as %_
          iapply HΦ; ipureintro; word
        · wp_apply wp_Assume as %h
          cases h
      · wp_apply wp_Assume as %h
        cases h
  · wp_if_destruct
    · wp_if_destruct
      · wp_apply wp_Assume as %_
        iapply HΦ; ipureintro; word
      · wp_apply wp_Assume as %h
        cases h
    · wp_apply wp_Assume as %h
      cases h

end proof

end Perennial
