/-
The proof of `catcher.catchAndRepanic'deferred` (a goose semantics test, `recover_deferred.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.catcher__catchAndRepanic'deferred

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.catcher.catchAndRepanic'deferred.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.catcher.catchAndRepanic'deferred.spec (GF := GF) (hG := hG) := by
  intro c pnc s w Φ
  iintro Hs Hpnc HΦ
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_recoverPanic $$ [$Hpnc] as Hpnc
  wp_apply wp_panic
  iapply HΦ $$ [$Hs] [$Hpnc]

end proof

end Perennial
