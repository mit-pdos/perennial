/-
The proof of `repanicInner` (a goose semantics test, `recover_deferred.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.repanicInner
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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.repanicInner.wp_proof
    (wp_catchAndRepanic : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.catcher.catchAndRepanic'deferred.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.repanicInner.spec (GF := GF) (hG := hG) := by
  intro c s Φ
  iintro Hs HΦ
  wp_func_call
  wp_call
  wp_apply wp_with_defer_recover as %defer %pnc defer pnc
  wp_apply wp_panic
  wp_apply wp_catchAndRepanic $$ [$Hs] [$pnc]
  iintro Hs pnc
  wp_auto
  rw [show W64 5 + W64 1 = W64 6 by rfl]
  iapply HΦ $$ [$Hs]

end proof

end Perennial
