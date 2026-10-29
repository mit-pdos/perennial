/-
The proof of `(*Page).leafPageElements`: `unsafe.Slice` of the elements after the header.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page__leafPageElements
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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page.leafPageElements.wp_proof
    (wp_unsafeAdd : unsafeAdd.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page.leafPageElements.spec (GF := GF) (hG := hG) := by
  intro p hdr dq
  wp_start as ⟨Hp, %H⟩
  have hnn : p ≠ null := by intro h; subst h; simp [null] at H
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨Hid, Hflags, Hcount, Hoverflow, -⟩
  have hc : 0 ≤ uint.Z hdr.count' := by simp [uint.Z]
  have h16 : sint.Z (W64 16) = 16 := rfl
  wp_auto
  wp_if_destruct
  · rw [if_pos Hif]
    iapply HΦ
    iapply typedPointsto_combine _ _ _ hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  · wp_apply wp_unsafeAdd
    · ipureintro; rw [h16]; simp only [Loc.add]; omega
    wp_func_call
    wp_call
    have hcl := hdr.count'.isLt
    have hz : sint.Z (W64 (uint.Z hdr.count')) = uint.Z hdr.count' := by
      simp only [uint.Z] at *; word
    have h1 : ¬ sint.Z (W64 (uint.Z hdr.count')) < 0 := by omega
    have h2 : ¬ (p +ₗ sint.Z (W64 16) = null) := by
      rw [h16]; intro h; have := congrArg Loc.addr h; simp only [Loc.add, null] at this; omega
    have h3 : ¬ (2 ^ 64 < p.addr + sint.Z (W64 16) + sint.Z (W64 (uint.Z hdr.count')) *
        ((16 : Nat) : Int)) := by
      rw [hz, h16]; simp only [maxAddr] at H; omega
    simp only [h1, h2, h3, ite_false]
    wp_auto
    rw [if_neg Hif, h16]
    iapply HΦ
    iapply typedPointsto_combine _ _ _ hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe

end proof

end Perennial
