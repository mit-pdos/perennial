/-
The proof of `pageAt`: `&buf[off]` is `off` bytes past the slice's start.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.pageAt

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE
open github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.pageAt.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.pageAt.spec (GF := GF) (hG := hG) := by
  intro buf off
  wp_start as %H
  wp_auto
  simp only [show 0 ≤ sint.Z off ∧ sint.Z off < sint.Z buf.len from H.2, and_self, ite_true]
  wp_auto
  rw [sliceIndexRef_byte _ _ H.1 H.2.1]
  iapply HΦ
  itrivial

end proof

end Perennial
