/-
The proof of `slices.AppendSeq`: Perennial's `for range` rule over an iterator
(`wp_func_for_range1`), appending each element.
-/
module

public import Perennial.Spec.slices.AppendSeq

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

-- As in `marshal.WriteBool`: `wp_auto` would unfold the slice literal `[]E{v}`, but
-- `wp_slice_literal` expects it folded.
attribute [-instance] go.SliceSemantics.composite_literal_slice

theorem slices.AppendSeq.wp_proof : slices.AppendSeq.spec (GF := GF) (hG := hG) := by
  intro E _ _ Et _ S _ s vs seq R ok
  wp_start as ⟨Hs, Hcap, Hseq, HR⟩
  wp_auto
  wp_apply (wp_func_for_range1 seq R ok _ _) $$ Hseq HR
  iintro %xs %Hok
  iexists (fun i => iprop(∃ sl : GoSlice, s_ptr ↦ sl ∗ sl ↦* (vs ++ xs.take i) ∗
    ownSliceCap E sl (DFrac.own 1) ∗ (∃ vv : E, v_ptr ↦ vv) ∗ ⌜i = 0 → sl = s⌝))
  isplitl [s Hs Hcap v]
  · iexists s
    simp only [List.take_zero, List.append_nil]
    iframe
    ipureintro; intro; trivial
  isplitr
  · imodintro
    iintro %i %x %Hx ⟨%sl, s, Hs, Hcap, ⟨%vv, v⟩, -⟩
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_auto
    wp_apply wp_slice_append (V := E) (t := Et) sl _ _ _ _ $$ [$Hs $Hcap $Hsl1]
      as %s' ⟨Hs', Hcap', -⟩
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists s'
    iframe
    isplitl [Hs']
    · simp only [List.take_add_one, Hx, Option.toList_some, List.append_assoc]
      iexact Hs'
    ipureintro; omega
  · iintro ⟨%sl, s, Hs, Hcap, v, %Hnil⟩ HR
    rw [List.take_length]
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    refine ⟨Hok, fun h => Hnil (by simp [h])⟩

end proof

end Perennial
