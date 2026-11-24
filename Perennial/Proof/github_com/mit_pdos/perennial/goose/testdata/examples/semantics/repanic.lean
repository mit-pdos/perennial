/-
The proof of `repanic` (a goose semantics test, `recover_deferred.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.repanic
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.repanicInner

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.repanic.wp_proof
    (wp_repanicInner : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.repanicInner.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.repanic.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply wp_with_defer_recover as %defer %pnc defer pnc
  iStructNamed «$r0»
  wp_apply wp_repanicInner $$ [$seen]
  iintro seen
  wp_auto
  wp_apply wp_recoverPanic $$ [$pnc] as pnc
  rw [show W64 6 * W64 10 + (0 + W64 1) = W64 61 by rfl]
  iapply HΦ
  itrivial

end proof

end Perennial
