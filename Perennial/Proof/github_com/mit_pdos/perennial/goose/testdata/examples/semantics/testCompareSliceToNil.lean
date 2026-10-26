/-
The proof of `testCompareSliceToNil` (a goose semantics test, `nil.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testCompareSliceToNil

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testCompareSliceToNil.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testCompareSliceToNil.spec (GF := GF) (hG := hG) := by
  -- `make([]byte, 0)` points at an arbitrary non-null address (`GoPrealloc`)
  semantics_auto
  wp_apply wp_GoPrealloc as %p %hp
  steps
  have h : ¬ slice.mk p (W64 0) (W64 0) = slice.nil := by
    intro h; injection h with h1; exact hp h1
  simp only [h, decide_false, Bool.not_false]
  iexact HΦ

end proof

end Perennial
