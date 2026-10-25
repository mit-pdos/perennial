/-
The proof of `panicTwoDeep` (a goose semantics test, `recover.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.panicTwoDeep
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.panicInLoop

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.panicTwoDeep.wp_proof
    (wp_panicInLoop : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.panicInLoop.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.panicTwoDeep.spec (GF := GF) (hG := hG) := fun Φ => by
  iintro HΦ
  wp_func_call
  wp_call
  wp_apply wp_panicInLoop
  iexact HΦ

end proof

end Perennial
