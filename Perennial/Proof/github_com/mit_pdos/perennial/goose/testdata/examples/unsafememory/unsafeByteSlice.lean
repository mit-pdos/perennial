/-
The proof of `unsafeByteSlice`: `unsafe.Slice` of bytes below `maxAddr` does not overflow.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.unsafeByteSlice
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.unsafeAdd

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.unsafeByteSlice.wp_proof
    (wp_unsafeAdd : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.unsafeAdd.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.unsafeByteSlice.spec (GF := GF) (hG := hG) := by
  intro base off i j
  wp_start as %H
  wp_auto
  wp_apply wp_unsafeAdd
  · ipureintro; omega
  wp_func_call
  wp_call
  have h1 : ¬ sint.Z j < 0 := by omega
  have h2 : ¬ (base +ₗ sint.Z off = null) := by
    intro h; rw [h] at H; simp [null] at H
  have h3 : ¬ (2 ^ 64 < base.addr + sint.Z off + sint.Z j * ((1 : Nat) : Int)) := by
    simp only [Loc.add, maxAddr] at H; omega
  simp only [h1, h2, h3, ↓reduceIte]
  wp_auto
  simp only [show 0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z j ∧ sint.Z j ≤ sint.Z j from
    ⟨H.2.2.1, H.2.2.2, Int.le_refl _⟩]
  wp_auto
  simp only [slice.fullSlice]
  rw [sliceIndexRef_byte _ _ H.1 H.2.2.1]
  iapply HΦ
  itrivial

end proof

end Perennial
