/-
The proof of `(*leafPageElement).key`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.leafPageElement__key
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.unsafeByteSlice

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.leafPageElement.key.wp_proof
    (wp_unsafeByteSlice : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.unsafeByteSlice.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.leafPageElement.key.spec (GF := GF) (hG := hG) := by
  intro n e dq
  wp_start as ⟨Hn, %H⟩
  have hnn : n ≠ null := by intro h; subst h; simp [null] at H
  icases typedPointsto_split _ _ _ $$ Hn with Hn
  simp only [TypedPointsto.typedPointstoDef]
  icases Hn with ⟨Hflags, Hpos, Hksize, Hvsize, -⟩
  wp_auto
  have hp := e.pos'.isLt
  have hk := e.ksize'.isLt
  have h0 : sint.Z (W64 0) = 0 := rfl
  have h1 : sint.Z (W64 (uint.Z e.pos')) = uint.Z e.pos' := by simp only [uint.Z] at *; word
  have h2 : sint.Z (W64 (uint.Z e.pos') + W64 (uint.Z e.ksize')) =
      uint.Z e.pos' + uint.Z e.ksize' := by simp only [uint.Z] at *; word
  wp_apply wp_unsafeByteSlice
  · ipureintro; rw [h0, h1, h2, loc_add_0]; simp only [uint.Z] at *; omega
  rw [h0, h1, loc_add_0,
    show W64 (uint.Z e.pos') + W64 (uint.Z e.ksize') - W64 (uint.Z e.pos') = W64 (uint.Z e.ksize') by
      bv_omega]
  iapply HΦ
  iapply typedPointsto_combine _ _ _ hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end Perennial
