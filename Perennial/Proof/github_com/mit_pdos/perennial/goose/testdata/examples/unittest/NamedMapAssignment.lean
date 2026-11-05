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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unittest.NamedMapAssignment.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unittest.NamedMapAssignment.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  rw [go.make1_underlying, go.is_underlying (t := MapWrapper.ty)]
  wp_apply (wp_map_make1 (K := w64) (V := Bool)) with %m Hm
  wp_apply wp_mapInsert $$ Hm with Hm
  rw [GMap.insert_empty]
  wp_end

/-- A test of `go.delete_map` at a named map type (`MapWrapper`, `map[uint64]bool`): `delete(m, k)`
unfolds through `MapWrapper`'s underlying map type, as `len` does (`go.len_map`). -/
theorem github_com.mit_pdos.perennial.goose.testdata.examples.unittest.MapWrapper_delete
    (m : Loc) (M : GMap w64 Bool) (k : w64) :
    {{ (m ↦$ M : IProp GF) }}
      (App (App (Val #(functions go.delete [MapWrapper.ty])) (Val #m)) (Val #k))
    {{ RET #(); m ↦$ (GMap.delete k M) }} :=
  wp_mapDelete_underlying (t := MapWrapper.ty) m M k

end proof

end Perennial
