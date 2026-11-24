/-
The proof of `internal.gomodel.ChooseString`: translated Go over `Choose` and `ChooseUint64`.
-/
module

public import Perennial.Spec.internal.gomodel.ChooseString
public import Perennial.Spec.internal.gomodel.Choose
public import Perennial.Spec.internal.gomodel.ChooseUint64

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.gomodel.Assumptions]

theorem internal.gomodel.ChooseString.wp_proof
    (wp_Choose : internal.gomodel.Choose.spec (GF := GF) (hG := hG))
    (wp_ChooseUint64 : internal.gomodel.ChooseUint64.spec (GF := GF) (hG := hG)) :
    internal.gomodel.ChooseString.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  ihave IH : iprop(∃ (sl : GoSlice) (bs : List w8),
      "b" ∷ b_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* bs ∗
      "Hcap" ∷ ownSliceCap w8 sl (DFrac.own 1)) $$ [b]
  · iexists slice.nil, []
    iframe
    isplitl []
    · iapply ownSlice_nil
    · iapply ownSliceCap_nil
  wp_for IH
  wp_apply wp_Choose as %c -
  rcases c with _ | _ <;> simp only [intoVal_eq_iff, decide_false, decide_true,
    Bool.false_eq_true, ↓reduceIte]
  -- `false`: the loop ends
  · wp_auto
    wp_apply wp_bytes_to_string $$ Hsl as -
    iapply HΦ; itrivial
  -- `true`: one more element
  · wp_auto
    wp_apply wp_ChooseUint64 as %x -
    wp_apply wp_slice_literal (V := w8) [W8 (uint.Z x)]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [Hsl Hcap Hsl2] with %sl' ⟨Hsl, Hcap, -⟩
    · iframe
    wp_for_post
    iframe
    iexists _, _
    iframe

end proof

end Perennial
