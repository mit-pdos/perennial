/-
The proof of `testOverlappingLoads`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testOverlappingLoads

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

theorem testOverlappingLoads.wp_proof : testOverlappingLoads.spec (GF := GF) (hG := hG) := by
  unsafememory_auto
  icases typedPointsto_zero_byte_array p_ptr _ 24 _ (by decide) (by decide) $$ p with ⟨%Hl, p⟩
  have ix := fun i hi => sliceIndexRef_byte_W64 (slice.mk p_ptr (W64 24) (W64 24)) i Hl hi
  icases bytesPointsto_view_at (V := w8) p_ptr _ _ 8 _ (ix 8 (by decide)) (by simp) Hl $$ p
    with ⟨Hb, p⟩
  wp_auto
  ispecialize p $$ Hb
  icases bytesPointsto_view_read (V := InBucket) p_ptr _ _ 0 _ (ix 0 (by decide))
    (by simp [replaceBytes, encode_w8]) Hl $$ p
    with ⟨Hx, p⟩
  wp_auto
  ispecialize p $$ Hx
  icases bytesPointsto_view_read (V := InBucket) p_ptr _ _ 8 _ (ix 8 (by decide))
    (by simp [replaceBytes, encode_w8]) Hl $$ p
    with ⟨Hy, p⟩
  wp_auto
  iexact HΦ

end proof

end github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory

end Perennial
