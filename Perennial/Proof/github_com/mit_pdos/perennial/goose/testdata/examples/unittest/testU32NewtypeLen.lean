/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/unittest.testU32NewtypeLen`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.testU32NewtypeLen

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unittest.testU32NewtypeLen.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unittest.testU32NewtypeLen.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_apply (wp_slice_make2 (V := w8)) with %sl ⟨Hs, Hcap⟩
  · ipureintro; word
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  have h : sint.Z sl.len = 20 := by
    have h1 := Hlen.1
    have h2 := Hlen.2
    simp only [List.length_replicate] at h1
    word
  rw [decide_eq_true (by rw [h])]
  iapply HΦ
  itrivial

end proof

end Perennial
