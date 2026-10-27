/-
The proof of `testRangeStringCount` (a goose semantics test, `range_string.go`), from
`countRune`'s spec: `wp_auto` computes the runes of the two literals.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testRangeStringCount
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.countRune

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testRangeStringCount.wp_proof
    (wp_countRune : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.countRune.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testRangeStringCount.spec (GF := GF) (hG := hG) := by
  intro Φ
  iintro HΦ
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_countRune
  wp_apply wp_countRune
  iexact HΦ

end proof

end Perennial
