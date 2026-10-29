/-
The proof of `testDisjointStructCopy`: the 128-byte buffer split in two, each half viewed as a
`Meta`, so that whole-struct copies between and onto the views use the struct points-to.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testDisjointStructCopy

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testDisjointStructCopy.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testDisjointStructCopy.spec (GF := GF) (hG := hG) := by
  unsafememory_auto
  icases typedPointsto_zero_byte_array p_ptr _ 128 _ (by decide) (by decide) $$ p with ⟨%Hl, p⟩
  have ix := fun i hi => sliceIndexRef_byte_W64 (slice.mk p_ptr (W64 2 * W64 64) (W64 2 * W64 64))
    i Hl hi
  rw [show List.replicate 128 (0 : w8) = List.replicate 64 0 ++ List.replicate 64 0 from rfl]
  icases (bytesPointsto_app p_ptr _ _ _).1 $$ p with ⟨pa, pb⟩
  simp only [List.length_replicate]
  icases bytesPointsto_view_at (V := Meta) p_ptr _ _ 0 _ (ix 0 (by decide)) (by simp) Hl $$ pa
    with ⟨Ha, pa⟩
  icases bytesPointsto_view_at (V := Meta) (p_ptr +ₗ ((64 : Nat) : Int)) _ _ 0
    (sliceIndexRef w8 (sint.Z (W64 64)) (slice.mk p_ptr (W64 2 * W64 64) (W64 2 * W64 64)))
    ((ix 64 (by decide)).trans (by simp)) (by simp) (by simp [Loc.add]; omega) $$ pb with ⟨Hb, pb⟩
  wp_auto
  iexact HΦ

end proof

end Perennial
