/-
The proof of `internal.gomodel.ChooseStrings`: translated Go over `Choose` and `ChooseString`.
-/
module

public import Perennial.Spec.internal.gomodel.ChooseStrings
public import Perennial.Spec.internal.gomodel.ChooseString
public import Perennial.Spec.internal.gomodel.Choose

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

theorem internal.gomodel.ChooseStrings.wp_proof
    (wp_Choose : internal.gomodel.Choose.spec (GF := GF) (hG := hG))
    (wp_ChooseString : internal.gomodel.ChooseString.spec (GF := GF) (hG := hG)) :
    internal.gomodel.ChooseStrings.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  -- `a` starts `nil` or a non-nil empty slice (`[]string{}`)
  wp_apply wp_Choose as %c0 -
  rcases c0 with _ | _ <;> (try simp only [intoVal_eq_iff, _root_.decide_false, _root_.decide_true,
    Bool.false_eq_true, ↓reduceIte])
  · wp_auto
    ihave HI : iprop(∃ (sl : GoSlice) (xs : List GoString),
      "a" ∷ a_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* xs ∗
      "Hcap" ∷ ownSliceCap GoString sl (DFrac.own 1)) $$ [a]
    · iexists slice.nil, []
      iframe
      isplitl []
      · iapply ownSlice_nil
      · iapply ownSliceCap_nil
    wp_for HI
    wp_apply wp_Choose as %c -
    rcases c with _ | _ <;> simp only [intoVal_eq_iff, decide_false, decide_true,
      Bool.false_eq_true, ↓reduceIte]
    -- `false`: the loop ends
    · wp_auto
      iapply HΦ
      iexists _
      iframe
    -- `true`: one more element
    · wp_auto
      wp_apply wp_ChooseString as %str -
      wp_apply wp_slice_literal (V := GoString) [str]
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
  · wp_auto
    wp_apply wp_slice_literal (V := GoString) []
    isplitr
    · ipureintro; rfl
    iintro %sl0 ⟨Hsl0, Hcap0⟩
    wp_auto
    ihave HI : iprop(∃ (sl : GoSlice) (xs : List GoString),
      "a" ∷ a_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* xs ∗
      "Hcap" ∷ ownSliceCap GoString sl (DFrac.own 1)) $$ [a Hsl0 Hcap0]
    · iexists _, []
      iframe
    wp_for HI
    wp_apply wp_Choose as %c -
    rcases c with _ | _ <;> simp only [intoVal_eq_iff, decide_false, decide_true,
      Bool.false_eq_true, ↓reduceIte]
    -- `false`: the loop ends
    · wp_auto
      iapply HΦ
      iexists _
      iframe
    -- `true`: one more element
    · wp_auto
      wp_apply wp_ChooseString as %str -
      wp_apply wp_slice_literal (V := GoString) [str]
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
