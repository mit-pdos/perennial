/-
The proof of `catchTop'deferred` (a goose semantics test, `recover_deferred.go`).
-/
module

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.catchTop'deferred.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.catchTop'deferred.spec (GF := GF) (hG := hG) := by
  intro res pnc x w
  wp_start as ⟨Hres, Hpnc⟩
  wp_auto
  wp_apply wp_recoverPanic $$ [$Hpnc] as Hpnc
  iapply HΦ
  iframe

end proof

end Perennial
