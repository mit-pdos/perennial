/-
The proof of `testDefersOnlyRecovering` (a goose semantics test, `recover_deferred.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testDefersOnlyRecovering
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.defersOnlyRecovering

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testDefersOnlyRecovering.wp_proof
    (wp_defersOnlyRecovering : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.defersOnlyRecovering.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testDefersOnlyRecovering.spec (GF := GF) (hG := hG) := by
  intro Φ
  iintro HΦ
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_defersOnlyRecovering
  iexact HΦ

end proof

end Perennial
