/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/unittest.testConversionLiteral`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.testConversionLiteral

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unittest.testConversionLiteral.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unittest.testConversionLiteral.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply (wp_map_make1 (K := GoInterface) (V := GoInterface)) with %m Hm
  have hnil : SafeMapKey (GF := GF) go.any (interface.nil : GoInterface) :=
    ⟨fun s E Φ => by iintro H; wp_auto; iapply H⟩
  wp_apply wp_mapInsert $$ Hm with Hm
  wp_apply wp_mapInsert $$ Hm with Hm
  have hs : SafeMapKey (GF := GF) go.any
      (interface.mkOk withInterface.ty #(withInterface.mk interface.nil)) :=
    ⟨fun s E Φ => by iintro H; wp_auto; iapply H⟩
  wp_apply wp_mapInsert $$ Hm with Hm
  wp_apply wp_map_lookup1 $$ Hm with Hm
  wp_apply wp_map_lookup1 $$ Hm with Hm
  iapply HΦ
  itrivial

end proof

end Perennial
