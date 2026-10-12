/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/unittest.NamedMapAssignment`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.NamedMapAssignment

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unittest.NamedMapAssignment.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unittest.NamedMapAssignment.spec (GF := GF) (hG := hG) := by
  wp_start
  rw [go.make1_underlying, go.is_underlying (t := MapWrapper.ty)]
  wp_apply (wp_map_make1 (K := w64) (V := Bool)) with %m Hm
  wp_apply wp_mapInsert $$ Hm with Hm
  rw [GMap.insert_empty]
  wp_end

end proof

end Perennial
