/-
The proof of `generics.makeBox`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.makeBox

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.makeBox.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.makeBox.spec
      (GF := GF) (hG := hG) := by
  wp_start
  wp_end

end proof

end Perennial
