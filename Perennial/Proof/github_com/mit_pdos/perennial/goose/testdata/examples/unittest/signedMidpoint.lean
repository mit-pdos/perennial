/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/unittest.signedMidpoint`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.signedMidpoint

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unittest.signedMidpoint.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unittest.signedMidpoint.spec (GF := GF) (hG := hG) := fun x y => by
  wp_start as %H
  wp_auto
  iapply HΦ
  ipureintro
  simp only [sint.Z] at H ⊢
  rw [BitVec.toInt_sdiv_of_ne_or_ne _ _ (Or.inr (by decide)),
    BitVec.toInt_add_of_not_saddOverflow (by
      simp only [BitVec.saddOverflow, Bool.or_eq_true, decide_eq_true_eq, not_or, ge_iff_le,
        Int.not_le, Int.not_lt]
      omega)]
  rfl

end proof

end Perennial
