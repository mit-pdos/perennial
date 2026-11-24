/-
The proof of `strconv.appendQuotedWith`.
-/
module

public import Perennial.Spec.strconv.appendQuotedWith
public import Perennial.Spec.strconv.appendEscapedRune
public import Perennial.Spec.unicode.utf8.DecodeRuneInString
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base
public import Perennial.Proof.bytes.BufferBasics

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strconv.Assumptions]

attribute [-instance] go.SliceSemantics.composite_literal_slice

/-- Composing two undo wands. -/
private theorem appendQuotedWith.undo_comp {P Q R : IProp GF} : (P -∗ Q) ⊢ (Q -∗ R) -∗ (P -∗ R) := by
  iintro H1 H2 HP
  iapply H2
  iapply H1
  iexact HP

theorem strconv.appendQuotedWith.wp_proof
    (wp_appendEscapedRune : strconv.appendEscapedRune.spec (GF := GF) (hG := hG))
    (wp_DecodeRuneInString : unicode.utf8.DecodeRuneInString.spec (GF := GF) (hG := hG)) :
    strconv.appendQuotedWith.spec (GF := GF) (hG := hG) := by
  intro buf bs s quote ASCIIonly
  wp_start as ⟨Hb, Hcap⟩
  ihave #Hutf8 : isPkgInit (PROP := IProp GF) pkg_id.unicode.utf8 $$ []
  · iPkgInit
  ihave %Hblen := ownSlice_len _ _ _ $$ Hb
  ihave %Hbmax := bytes.ownSlice_bytes_len_le _ _ _ $$ Hb
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len_maxAddr as %Hs
  have Hslen : s.length < 2 ^ 63 := by unfold maxAddr at Hs; omega
  have hbl : (bs.length : Int) = sint.Z buf.len := by
    obtain ⟨h1, h2⟩ := Hblen; simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  wp_join iprop(∃ b : GoSlice, "buf" ∷ buf_ptr ↦ b ∗ "Hb" ∷ b ↦* bs ∗
      "Hcap" ∷ ownSliceCap w8 b (DFrac.own 1) ∗ "s" ∷ s_ptr ↦ s ∗
      "Hundo" ∷ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) -∗
        buf ↦* bs ∗ ownSliceCap w8 buf (DFrac.own 1))) with [buf Hb Hcap s]
      as ⟨%b0, buf, Hb, Hcap, s, Hundo⟩
  · try wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    try wp_auto
    wp_apply wp_slice_make3 (V := w8) (t := go.byte) _ _ ⟨by omega, by unfold maxAddr at *; word⟩
      as %nb ⟨Hnb, Hncap, %Hnbc⟩
    try wp_auto
    wp_apply wp_slice_copy (V := w8) (t := go.byte) nb _ buf bs (DFrac.own 1) $$ [$Hnb $Hb]
      as %n ⟨%Hn, Hnb, Hbo⟩
    have hl : (List.replicate (sint.nat buf.len) (zero_val w8)).length = bs.length := by
      simp only [List.length_replicate]; omega
    rw [hl, List.take_length, List.drop_eq_nil_of_le (by omega), List.append_nil]
    try wp_auto
    ihave Hundo : (nb ↦* bs ∗ ownSliceCap w8 nb (DFrac.own 1) -∗
        buf ↦* bs ∗ ownSliceCap w8 buf (DFrac.own 1)) $$ [Hbo Hcap]
    · iintro -; iframe
    wp_join_done
  all_goals try (iexists buf; iframe; iintro H; iexact H; done)
  all_goals (
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    try wp_auto
    wp_apply wp_slice_append_undo (V := w8) (t := go.byte) _ _ _ _ _ $$ [$Hb $Hcap $Hsl]
      as %b' ⟨Hb, Hcap, -, Hu⟩
    ihave Hundo := appendQuotedWith.undo_comp $$ Hu Hundo
    try wp_auto
    ihave HI : (∃ (sv : GoString) (b : GoSlice) (q : List w8) (rv : w32) (wv : w64),
        "s" ∷ s_ptr ↦ sv ∗ "buf" ∷ buf_ptr ↦ b ∗ "Hb" ∷ b ↦* bs ++ q ∗
        "Hcap" ∷ ownSliceCap w8 b (DFrac.own 1) ∗ "r" ∷ r_ptr ↦ rv ∗ "width" ∷ width_ptr ↦ wv ∗
        "Hundo" ∷ (b ↦* bs ++ q ∗ ownSliceCap w8 b (DFrac.own 1) -∗
          buf ↦* bs ∗ ownSliceCap w8 buf (DFrac.own 1)) ∗
        "%Hsv" ∷ ⌜sv.length ≤ s.length⌝ : IProp GF) $$ [s buf Hb Hcap r width Hundo]
    · iexists _, _, _, _, _
      iframe
      ipureintro; exact Nat.le_refl _
    wp_for HI
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hsvlen
    wp_if_destruct
    · have hne : sv ≠ [] := by
        intro h; subst h; exact absurd (go.intoVal_inj Hif) (by decide)
      obtain ⟨c, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
      wp_apply wp_DecodeRuneInString as %rv' %wv' %Hw
      have hw : 1 ≤ sint.Z wv' ∧ sint.Z wv' ≤ (c :: rest).length := by
        rcases Hw.1 with ⟨h, -⟩ | ⟨-, h⟩
        · exact absurd h (List.cons_ne_nil _ _)
        · exact h
      repeat' (first
        | wp_if_destruct
        | wp_auto
        | (simp only [strconv.lowerhex_get, strconv.lowerhex_get', strconv.lowerhex_idx_shr_w8_lo,
            strconv.lowerhex_idx_shr_w8_hi, strconv.lowerhex_idx_and_w8_lo, strconv.lowerhex_idx_and_w8_hi,
            _root_.and_self, ↓reduceIte])
        | (wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
           wp_apply wp_slice_append_undo (V := w8) (t := go.byte) _ _ _ _ _ $$ [$Hb $Hcap $Hsl]
             as %b' ⟨Hb, Hcap, -, Hu⟩
           ihave Hundo := appendQuotedWith.undo_comp $$ Hu Hundo)
        | (wp_apply wp_slice_literal
           isplitr
           ipureintro
           rfl
           iintro %sl ⟨Hsl, -⟩
           wp_auto
           wp_apply wp_slice_append_undo (V := w8) (t := go.byte) _ _ _ _ _ $$ [$Hb $Hcap $Hsl]
             as %b' ⟨Hb, Hcap, -, Hu⟩
           ihave Hundo := appendQuotedWith.undo_comp $$ Hu Hundo)
        | (wp_apply wp_appendEscapedRune $$ [$Hb $Hcap] as %b' ⟨%q', Hb, Hcap, Hu⟩
           ihave Hundo := appendQuotedWith.undo_comp $$ Hu Hundo))
      all_goals (
        wp_for_post
        wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
        have hlenW : sint.Z (W64 ((c :: rest).length : Int)) = (c :: rest).length := by
          simp only [List.length_cons] at *; word
        rw [ite_eq_left ⟨by omega, by omega, by omega⟩]
        try wp_auto
        iframe
        iexists _, _, _, _, _
        try simp only [List.append_assoc]
        iframe
        ipureintro
        simp only [List.length_take, List.length_drop, List.length_cons] at *
        omega)
    · have hc : ¬ sint.Z (W64 0) < sint.Z (W64 (sv.length : Int)) :=
        fun h => Hif (by rw [decide_eq_true h])
      simp only [decide_eq_false hc, Bool.false_eq_true, ↓reduceIte]
      wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_auto
      wp_apply wp_slice_append_undo (V := w8) (t := go.byte) _ _ _ _ _ $$ [$Hb $Hcap $Hsl]
        as %b' ⟨Hb, Hcap, -, Hu⟩
      ihave Hundo := appendQuotedWith.undo_comp $$ Hu Hundo
      try wp_auto
      try simp only [List.append_assoc]
      iapply HΦ
      iexists _
      iframe)

end proof

end Perennial
