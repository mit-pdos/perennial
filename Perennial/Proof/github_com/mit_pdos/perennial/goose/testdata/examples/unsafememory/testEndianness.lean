/-
The proof of `testEndianness`: a `Page` view over 16 bytes; its fields are the bytes at gc's
offsets, little-endian.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testEndianness

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testEndianness.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testEndianness.spec (GF := GF) (hG := hG) := by
  unsafememory_auto
  icases typedPointsto_zero_byte_array p_ptr _ 16 _ (by decide) (by decide) $$ p with ⟨%Hl, pb⟩
  have ix := fun i hi => sliceIndexRef_byte_W64 (slice.mk p_ptr (W64 16) (W64 16)) i Hl hi
  icases bytesPointsto_view_at (V := w8) p_ptr _ _ 0 _ (ix 0 (by decide)) (by simp) Hl $$ pb
    with ⟨Hb, pb⟩
  wp_pures
  wp_store
  ispecialize pb $$ Hb
  icases bytesPointsto_view_at (V := w8) p_ptr _ _ 9 _ (ix 9 (by decide))
    (by simp [replaceBytes, encode_w8]) Hl $$ pb with ⟨Hb, pb⟩
  wp_auto
  ispecialize pb $$ Hb
  unsafememory_steps
  icases bytesPointsto_view_at (V := Page) _ _ _ 0 _ (ix 0 (by decide))
    (by simp [replaceBytes, encode_w8]) Hl $$ pb with ⟨Hp, pb⟩
  wp_auto
  ispecialize pb $$ Hp
  icases bytesPointsto_congr _ _ _
    [W8 1, W8 0, W8 0, W8 0, W8 0, W8 0, W8 0, W8 0, W8 0, W8 2, W8 2, W8 1, W8 6, W8 5, W8 4, W8 3]
    (by simp [replaceBytes, encode, decode, ByteEncoding.encode, ByteEncoding.decode, natBytes, bytesNat]) $$ pb with pb
  icases bytesPointsto_view_read (V := w8) _ _ _ 10 _ (ix 10 (by decide)) (by simp) Hl $$ pb
    with ⟨Hb, pb⟩
  wp_auto
  ispecialize pb $$ Hb
  icases bytesPointsto_view_read (V := w8) _ _ _ 11 _ (ix 11 (by decide)) (by simp) Hl $$ pb
    with ⟨Hb, pb⟩
  wp_auto
  ispecialize pb $$ Hb
  icases bytesPointsto_view_read (V := w8) _ _ _ 12 _ (ix 12 (by decide)) (by simp) Hl $$ pb
    with ⟨Hb, pb⟩
  wp_auto
  ispecialize pb $$ Hb
  icases bytesPointsto_view_read (V := w8) _ _ _ 13 _ (ix 13 (by decide)) (by simp) Hl $$ pb
    with ⟨Hb, pb⟩
  wp_auto
  ispecialize pb $$ Hb
  icases bytesPointsto_view_read (V := w8) _ _ _ 14 _ (ix 14 (by decide)) (by simp) Hl $$ pb
    with ⟨Hb, pb⟩
  wp_auto
  ispecialize pb $$ Hb
  icases bytesPointsto_view_read (V := w8) _ _ _ 15 _ (ix 15 (by decide)) (by simp) Hl $$ pb
    with ⟨Hb, pb⟩
  wp_auto
  ispecialize pb $$ Hb
  iexact HΦ

end proof

end Perennial
