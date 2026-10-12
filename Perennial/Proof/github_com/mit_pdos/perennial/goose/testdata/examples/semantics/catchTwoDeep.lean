/-
The proof of `catchTwoDeep` (a goose semantics test, `recover.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.catchTwoDeep
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.panicTwoDeep

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.catchTwoDeep.wp_proof
    (wp_panicTwoDeep : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.panicTwoDeep.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.catchTwoDeep.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply wp_with_defer_recover as %defer %pnc defer pnc
  wp_apply wp_panicTwoDeep
  wp_apply wp_recoverPanic $$ [$pnc] as pnc
  iapply HΦ
  itrivial

end proof

end Perennial
