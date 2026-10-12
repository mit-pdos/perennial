/-
The proof of `testOpAssignIndexOnce` (a goose semantics test, `evalorder.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testOpAssignIndexOnce

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testOpAssignIndexOnce.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testOpAssignIndexOnce.spec (GF := GF) (hG := hG) := by
  semantics_auto
  icases array_acc (GF := GF) _ (sint.Z (W64 0)) _ _ _ (W64 1) (by decide) rfl $$ a with ⟨Ha0, a⟩
  steps
  ihave a := a $$ Ha0
  simp only [show (sint.Z (W64 0)).toNat = 0 from rfl, List.set_cons_zero]
  icases array_acc (GF := GF) _ (sint.Z (W64 0)) _ _ _ _ (by decide) rfl $$ a with ⟨Ha0, a⟩
  steps
  ihave a := a $$ Ha0
  icases array_acc (GF := GF) _ (sint.Z (W64 1)) _ _ _ (W64 1) (by decide) rfl $$ a with ⟨Ha1, a⟩
  steps
  iexact HΦ

end proof

end Perennial
