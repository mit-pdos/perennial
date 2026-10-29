/-
The proof of `testAddPastEnd`: `unsafe.Add` one past the end of a 16-byte buffer is not nil, since
the buffer is at an address in `(0, maxAddr)` and the addition does not wrap.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testAddPastEnd

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testAddPastEnd.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testAddPastEnd.spec (GF := GF) (hG := hG) := by
  unsafememory_auto
  ihave %Hb := typedPointsto_byte_array_bounds _ _ _ _
    (by simp [zero_val, ZeroVal.zeroValDef]; decide) $$ p
  have e : arrayIndexRef w8 (sint.Z (W64 0)) p_ptr = p_ptr := go.arrayIndexRef_0 _ _
  have e16 : sint.Z (W64 16) = 16 := rfl
  wp_apply wp_pointer_plus _ _ _
    (by simp only [sliceIndexRef, e, e16, Loc.add, maxAddr] at Hb ⊢; omega)
  unsafememory_steps
  iapply github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.exact_eq ?_ $$ HΦ
  simp only [sliceIndexRef, e, e16]
  have hne : ¬ (p_ptr +ₗ 16 = null) := by
    simp only [null, Loc.add, Loc.mk.injEq]
    omega
  simp only [hne, decide_false, Bool.not_false]

end proof

end Perennial
