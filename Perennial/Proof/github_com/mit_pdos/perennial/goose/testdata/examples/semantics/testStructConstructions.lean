/-
The proof of `testStructConstructions` (a goose semantics test, `structs.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testStructConstructions

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testStructConstructions.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testStructConstructions.spec (GF := GF) (hG := hG) := by
  semantics_auto
  by_cases h : p4_ptr = «$r0_ptr»
  · -- Both full points-tos are for the same location: contradiction, via the
    -- first fields' `w64` points-tos.
    subst h
    iexfalso
    rw [typedPointsto_unseal_eq p4_ptr (_ : TwoInts), typedPointsto_unseal_eq p4_ptr (_ : TwoInts)]
    simp only [TypedPointsto.typedPointstoDef]
    icases p4 with ⟨⟨Hx, _⟩, _⟩
    icases «$r0» with ⟨⟨Hx', _⟩, _⟩
    iapply w64_pointsto_excl
    iframe
  · simp only [h, decide_false, Bool.not_false]
    iexact HΦ

end proof

end Perennial
