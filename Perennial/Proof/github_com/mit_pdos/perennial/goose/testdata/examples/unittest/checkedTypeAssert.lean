/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/unittest.checkedTypeAssert`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.checkedTypeAssert

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unittest.checkedTypeAssert.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unittest.checkedTypeAssert.spec (GF := GF) (hG := hG) := fun x => by
  wp_start as %Htype
  wp_auto
  cases x with
  | nil =>
    dsimp only
    wp_auto
    wp_end
  | ok i =>
    obtain ⟨ty, v⟩ := i
    by_cases h : ty = go.uint64
    · subst h
      simp only [eq_self, ite_true] at Htype
      obtain ⟨v', rfl⟩ := Htype
      wp_auto
      wp_end
    · wp_auto_neg h
      wp_end

end proof

end Perennial
