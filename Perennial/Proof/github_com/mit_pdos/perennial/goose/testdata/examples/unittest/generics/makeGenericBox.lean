/-
The proof of `generics.makeGenericBox`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.makeGenericBox

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.makeGenericBox.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.makeGenericBox.spec
      (GF := GF) (hG := hG) := by
  intro T' _ _ T _ value
  wp_start
  wp_auto
  wp_end

end proof

end Perennial
