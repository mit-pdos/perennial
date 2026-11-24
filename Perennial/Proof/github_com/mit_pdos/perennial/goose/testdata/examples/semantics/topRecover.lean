/-
The proof of `topRecover` (a goose semantics test, `recover_deferred.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.topRecover
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.catchTop'deferred

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.topRecover.wp_proof
    (wp_catchTop : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.catchTop'deferred.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.topRecover.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply wp_with_defer_recover as %defer %pnc defer pnc
  wp_apply wp_panic
  wp_apply wp_catchTop $$ [$x $pnc] as ⟨x, pnc⟩
  iapply HΦ
  itrivial

end proof

end Perennial
