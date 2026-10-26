/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/unittest.basicTypeSwitch`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.basicTypeSwitch

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unittest.basicTypeSwitch.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unittest.basicTypeSwitch.spec (GF := GF) (hG := hG) := fun x => by
  wp_start as %Htype
  wp_auto
  cases x with
  | nil =>
    dsimp only
    wp_auto
    wp_end
  | ok i =>
    obtain ⟨ty, v⟩ := i
    by_cases h : ty = go.int
    · subst h
      -- (the asserted value is bound by a `let:`, so it must not be a panic)
      obtain ⟨v', rfl⟩ := Htype.1 rfl
      wp_auto
      wp_end
    · wp_auto_neg h
      by_cases h' : ty = go.string
      · subst h'
        obtain ⟨v', rfl⟩ := Htype.2 rfl
        wp_auto
        wp_end
      · wp_auto_neg h'
        wp_end

end proof

end Perennial
