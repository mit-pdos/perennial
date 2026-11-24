/-
The proof of `internal.bytealg.MakeNoZero`, from its trusted model `MakeNoZero.impl`
(`Perennial/TrustedCode/internal/bytealg.lean`).
-/
module

public import Perennial.Spec.internal.bytealg.MakeNoZero

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace internal.bytealg

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

set_option maxHeartbeats 2000000 in
/-- The model's `fillArbitrary s i`: an arbitrary byte in each element of `s` from `i` on. -/
theorem wp_fillArbitrary :
    ⊢ ∀ (s : GoSlice) (vs : List w8) (i : w64) (Φ : val → IProp GF),
      ⌜0 ≤ sint.Z i⌝ -∗ (s ↦* vs : IProp GF) -∗
      (∀ vs' : List w8, s ↦* vs' -∗ ⌜vs'.length = vs.length⌝ -∗ Φ #()) -∗
      WP (App (App (Val fillArbitrary) (Val #s)) (Val #i)) {{ Φ }} := by
  unfold fillArbitrary
  iloeb as IH
  iintro %s %vs %i %Φ %Hi Hs HΦ
  ihave %Hlen := ownSlice_len $$ Hs
  wp_pures
  wp_if_destruct
  · wp_pures
    rw [if_pos ⟨Hi, by word⟩]
    wp_apply wp_ArbitraryInt as %x -
    wp_pures
    wp_apply +noauto (wp_store_slice_index s (sint.Z i) vs (W8 (uint.Z x)) (V := w8)
      (t := go.byte)) $$ [$Hs] as Hs
    · ipureintro; constructor <;> word
    -- four pure steps, to the recursive call but not into it (`wp_pures` would take that too)
    wp_pure; wp_pure; wp_pure; wp_pure
    iapply IH $$ %s %_ %(i + W64 1) %Φ %(by word) Hs
    iintro %vs' Hs %Hl
    iapply HΦ $$ Hs
    ipureintro; rw [Hl, List.length_set]
  · iapply HΦ $$ Hs
    ipureintro; rfl

end wps

end internal.bytealg

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

set_option maxHeartbeats 2000000 in
theorem internal.bytealg.MakeNoZero.wp_proof :
    internal.bytealg.MakeNoZero.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start as %Hn
  wp_pures
  wp_apply wp_new_cap as %c %Hc
  wp_apply (wp_slice_make3 (V := w8) n c ⟨Hn, Hc⟩) as %b ⟨Hb, Hcap, %Hbc⟩
  ihave %Hblen := ownSlice_len $$ Hb
  ihave %Hbwf := ownSlice_wf b _ _ $$ Hb
  icases ownSlice_slice_into_capacity (W64 0) b.cap b _ $$ [$Hb $Hcap] with ⟨%vc, -, Hfull, Hcapf⟩
  · ipureintro; refine ⟨by decide, by word, Hbwf.2, Int.le_refl _⟩
  wp_pures
  rw [if_pos ⟨by decide, by word, Int.le_refl _⟩]
  wp_bind (App (App (Val internal.bytealg.fillArbitrary) _) _)
  iapply internal.bytealg.wp_fillArbitrary $$ %_ %_ %(W64 0) %_ %(by decide) Hfull
  iintro %vs' Hfull %-
  ihave %Hflen := ownSlice_len $$ Hfull
  wp_pures
  rw [← List.take_append_drop (sint.nat b.len) vs']
  have htl : (vs'.take (sint.nat b.len)).length = sint.nat b.len := by
    rw [List.length_take]; simp only [slice.slice] at Hflen; word
  ihave ⟨Hb, Hcap⟩ := ownSlice_append_undo_in_place b (vs'.take (sint.nat b.len))
    (vs'.drop (sint.nat b.len)) b.cap ⟨Hbwf.1, Hbwf.2, Int.le_refl _⟩ htl $$ [$Hfull $Hcapf]
  iapply HΦ
  iframe Hb Hcap
  ipureintro
  rw [htl]
  rw [List.length_replicate] at Hblen
  exact Hblen.1.symm

end proof

end Perennial
