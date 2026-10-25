/-
The proof of `testPrimitiveTypesEqual` (a goose semantics test, `type_equality.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testPrimitiveTypesEqual

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testPrimitiveTypesEqual.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testPrimitiveTypesEqual.spec (GF := GF) (hG := hG) := by
  semantics_auto

end proof

end Perennial
