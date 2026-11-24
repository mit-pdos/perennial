/-
The proof of `internal.bytealg.MakeNoZero`, translated from its Go model
(`goose/model/overlay/internal/bytealg/bytealg.go`).
-/
module

public import Perennial.Spec.internal.bytealg.MakeNoZero
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
variable [package_sem : internal.bytealg.Assumptions]

set_option maxHeartbeats 2000000 in
theorem internal.bytealg.MakeNoZero.wp_proof
    (wp_ChooseUint64 : internal.gomodel.ChooseUint64.spec (GF := GF) (hG := hG)) :
    internal.bytealg.MakeNoZero.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start as %Hn
  wp_auto
  wp_apply wp_ChooseUint64 as %x -
  try wp_auto
  wp_join iprop(∃ c : w64, c_ptr ↦ c ∗ n_ptr ↦ n ∗ ⌜sint.Z n ≤ sint.Z c⌝) with [c n]
    as ⟨%c, c, n, %Hc⟩
  · try wp_auto
    try wp_join_done
    iexists n
    iframe
    ipureintro; exact Int.le_refl _
  · iexists _
    iframe
    ipureintro; omega
  try wp_auto
  wp_apply (wp_slice_make3 (V := w8) n c ⟨Hn, Hc⟩) as %b ⟨Hb, Hcap, %Hbc⟩
  ihave %Hblen := ownSlice_len $$ Hb
  ihave %Hbwf := ownSlice_wf b _ _ $$ Hb
  try wp_auto
  icases ownSlice_slice_into_capacity (W64 0) b.cap b _ $$ [$Hb $Hcap] with ⟨%vc, -, Hfull, Hcapf⟩
  · ipureintro; refine ⟨by decide, by word, Hbwf.2, Int.le_refl _⟩
  rw [if_pos ⟨by decide, by word, Int.le_refl _⟩]
  ihave %Hflen := ownSlice_len $$ Hfull
  have Hsl : (slice.slice b w8 (W64 0) b.cap).len = b.cap := by simp [slice.slice]
  rw [Hsl] at Hflen
  try wp_auto
  -- `for i := range full { full[i] = byte(gomodel.ChooseUint64()) }`; `ki` is the loop's own counter
  rename_i ki_ptr
  irename : (ki_ptr ↦ zero_val w64 : IProp GF) => ki
  ihave HI : iprop(∃ (j kv : w64) (vs : List w8),
      "i" ∷ i_ptr ↦ j ∗ "ki" ∷ ki_ptr ↦ kv ∗
      "Hfull" ∷ slice.slice b w8 (W64 0) b.cap ↦* vs ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z b.cap⌝ ∗
      "%Hvs" ∷ ⌜vs.length = sint.nat b.cap⌝) $$ [i ki Hfull]
  · iexists _, _, _
    iframe
    ipureintro
    exact ⟨⟨by word, by word⟩, Hflen.1⟩
  wp_for HI
  split
  · rename_i Hif
    replace Hif := of_decide_eq_true Hif
    rw [show b.cap - W64 0 = b.cap by word] at Hif
    have Hlt : sint.nat j < vs.length := by word
    obtain ⟨v, Hv⟩ : ∃ v, vs[sint.nat j]? = some v := ⟨_, List.getElem?_eq_getElem Hlt⟩
    wp_auto
    rw [ite_eq_left (by word)]
    wp_apply wp_load_slice_index _ (sint.Z j) vs _ v Hj.1 $$ [Hfull] as Hfull
    · iframe; ipureintro; exact Hv
    try wp_auto
    wp_apply wp_ChooseUint64 as %y -
    try wp_auto
    rw [ite_eq_left (by word)]
    wp_apply (wp_store_slice_index _ (sint.Z j) vs _ (V := w8) (t := go.byte)) $$ [$Hfull]
      as Hfull
    · ipureintro; constructor <;> word
    try wp_auto
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    ipureintro
    refine ⟨⟨by word, by word⟩, by simp [Hvs]⟩
  · rename_i Hif
    try wp_auto
    rw [← List.take_append_drop (sint.nat b.len) vs]
    have htl : (vs.take (sint.nat b.len)).length = sint.nat b.len := by
      rw [List.length_take]; word
    ihave ⟨Hb, Hcap⟩ := ownSlice_append_undo_in_place b (vs.take (sint.nat b.len))
      (vs.drop (sint.nat b.len)) b.cap ⟨Hbwf.1, Hbwf.2, Int.le_refl _⟩ htl $$ [$Hfull $Hcapf]
    iapply HΦ
    iframe Hb Hcap
    ipureintro
    rw [htl]
    rw [List.length_replicate] at Hblen
    exact Hblen.1.symm

end proof

end Perennial
