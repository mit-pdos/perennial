/-
The proof of `bytes.Buffer.Read`.
-/
module

public import Perennial.Spec.bytes.Buffer__Read

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : bytes.Assumptions]

theorem bytes.Buffer.Read.wp_proof :
    bytes.Buffer.Read.spec (GF := GF) (hG := hG) := by
  intro l bs p xs eof
  wp_start as ⟨#Heof, Hown, Hp⟩
  unfold bytes.ownBuffer
  icases Hown with ⟨%b, %all, Hl, Hbuf, Hcap, %Hoff⟩
  ihave %Hlen := ownSlice_len $$ Hbuf
  ihave %Hwf := ownSlice_wf $$ Hbuf
  ihave %Hplen := ownSlice_len $$ Hp
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
  obtain ⟨bb, off, lr⟩ := b
  simp only at Hoff Hlen Hwf ⊢
  iStructNamed Hl
  wp_auto
  simp only [bytes.opInvalid, bytes.opRead]
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_if_destruct
  · -- the buffer is empty: `Reset`, then `0, nil` or `0, EOF`
    have Hbs : bs = [] := by
      rw [Hoff.2.2]; apply List.drop_eq_nil_of_le; word
    subst Hbs
    wp_method_call
    wp_call
    wp_auto
    simp only [bytes.opInvalid]
    have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 0) ∧
        sint.Z (W64 0) ≤ sint.Z bb.cap := ⟨by decide, by decide, by word⟩
    simp only [Hb0, _root_.and_self, ↓reduceIte]
    wp_auto
    icases ownSlice_slice_with_cap (W64 0) (W64 0) bb all ⟨by decide, by decide, by word⟩
      $$ [$Hbuf $Hcap] with ⟨Hbuf, -, Hcap⟩
    wp_if_destruct
    · -- `len(p) == 0`
      iapply HΦ
      have Hxs : xs = [] := by
        apply List.eq_nil_of_length_eq_zero; word
      subst Hxs
      simp only [List.take_nil, List.length_nil, List.drop_nil, List.nil_append]
      iframe Hp
      isplitr
      · ipureintro; exact ⟨by word, by simp⟩
      iexists ⟨slice.slice bb w8 (W64 0) (W64 0), W64 0, W8 0⟩, all.take (sint.nat (W64 0))
      iframe Hbuf Hcap
      isplitl
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ipureintro
      exact ⟨by word, by simp, by simp⟩
    · iapply HΦ
      simp only [List.take_nil, List.length_nil, List.drop_nil, List.nil_append, List.drop_zero]
      iframe Hp
      isplitr
      · ipureintro
        refine ⟨by word, Or.inr ⟨by simp, by simp, ?_⟩⟩
        intro h; subst h
        have h0 : sint.Z p.len = 0 := by
          have h := Hplen.1; have h' := Hplen.2; simp only [List.length_nil] at h; word
        have : p.len = W64 0 := by word
        simp [this] at Hif
      iexists ⟨slice.slice bb w8 (W64 0) (W64 0), W64 0, W8 0⟩, all.take (sint.nat (W64 0))
      iframe Hbuf Hcap
      isplitl
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ipureintro
      exact ⟨by word, by simp, by simp⟩
  · -- copy `buf[off:]` into `p`
    have Hb : 0 ≤ sint.Z off ∧ sint.Z off ≤ sint.Z bb.len ∧ sint.Z bb.len ≤ sint.Z bb.cap :=
      ⟨Hoff.1, by word, Hwf.2⟩
    simp only [Hb, _root_.and_self, ↓reduceIte]
    icases (ownSlice_split_all off bb _ _ ⟨Hoff.1, by word⟩).1 $$ Hbuf with ⟨Hbuf1, Hbuf2⟩
    rw [← Hoff.2.2]
    wp_apply wp_slice_copy_int $$ [Hp Hbuf2] as %n ⟨%HnZ, Hp, Hbuf2⟩
    · iframe
    have Hn : sint.nat n = min xs.length bs.length := by
      rw [show sint.nat n = (sint.Z n).toNat from rfl, HnZ]; simp
    have Hbsl : bs.length = all.length - sint.nat off := by rw [Hoff.2.2, List.length_drop]
    have Hk : (bs.take xs.length).length = sint.nat n := by
      rw [List.length_take, Hn]
    have Hdrop : xs.drop bs.length = xs.drop (bs.take xs.length).length := by
      rw [List.length_take]
      rcases Nat.le_total bs.length xs.length with h | h
      · rw [Nat.min_eq_right h]
      · rw [Nat.min_eq_left h, List.drop_eq_nil_of_le h, List.drop_length]
    have Hoffn : sint.nat (off + n) = sint.nat off + sint.nat n := by
      have : sint.nat n ≤ all.length - sint.nat off := by omega
      have e1 : (sint.nat off : Int) = sint.Z off := by word
      have h1 : sint.Z n ≤ bs.length := by rw [HnZ]; omega
      have : sint.Z n ≤ (all.length : Int) - sint.Z off := by omega
      have : 0 ≤ sint.Z n := by rw [HnZ]; omega
      word
    have Hrest : bs.drop xs.length = all.drop (sint.nat (off + n)) := by
      rw [Hoffn, ← List.drop_drop, ← Hoff.2.2, Hn]
      rcases Nat.le_total bs.length xs.length with h | h
      · rw [Nat.min_eq_right h, List.drop_eq_nil_of_le h, List.drop_length]
      · rw [Nat.min_eq_left h]
    ihave Hbuf := ownSlice_combine (GF := GF) (V := w8) off bb (DFrac.own 1) _ bs (W64 0) bb.len
      ⟨by rw [List.length_take]; word, by decide, Hoff.1, by word⟩ $$ Hbuf1 Hbuf2
    rw [Hoff.2.2, List.take_append_drop] at *
    ihave Hbuf := ownSlice_trivial_slice_2 $$ Hbuf
    wp_if_destruct
    · iapply HΦ
      rw [← Hdrop]
      iframe Hp
      isplitr
      · ipureintro; exact ⟨by word, by simp⟩
      iexists ⟨bb, off + n, W8 (-1)⟩, all
      iframe Hbuf Hcap
      isplitl
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ipureintro
      simp only
      refine ⟨by word, by word, ?_⟩
      rw [← Hoff.2.2]; exact Hrest
    · iapply HΦ
      rw [← Hdrop]
      iframe Hp
      isplitr
      · ipureintro; exact ⟨by word, by simp⟩
      iexists ⟨bb, off + n, W8 0⟩, all
      iframe Hbuf Hcap
      isplitl
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ipureintro
      simp only
      refine ⟨by word, by word, ?_⟩
      rw [← Hoff.2.2]; exact Hrest

end proof

end Perennial
