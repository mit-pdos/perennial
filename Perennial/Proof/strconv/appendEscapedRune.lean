/-
The proof of `strconv.appendEscapedRune`.
-/
module

public import Perennial.Spec.strconv.appendEscapedRune
public import Perennial.Spec.strconv.IsPrint
public import Perennial.Spec.unicode.utf8.AppendRune
public import Perennial.Spec.unicode.utf8.ValidRune

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
private theorem appendEscapedRune.undo_comp {P Q R : IProp GF} :
    (P -∗ Q) ⊢ (Q -∗ R) -∗ (P -∗ R) := by
  iintro H1 H2 HP
  iapply H2
  iapply H1
  iexact HP

set_option maxHeartbeats 2000000 in
theorem strconv.appendEscapedRune.wp_proof
    (wp_IsPrint : strconv.IsPrint.spec (GF := GF) (hG := hG))
    (wp_AppendRune : unicode.utf8.AppendRune.spec (GF := GF) (hG := hG))
    (wp_ValidRune : unicode.utf8.ValidRune.spec (GF := GF) (hG := hG)) :
    strconv.appendEscapedRune.spec (GF := GF) (hG := hG) := by
  intro buf bs r quote ASCIIonly
  wp_start as ⟨Hb, Hcap⟩
  ihave Hundo : (buf ↦* bs ∗ ownSliceCap w8 buf (DFrac.own 1) -∗
      buf ↦* bs ∗ ownSliceCap w8 buf (DFrac.own 1)) $$ []
  · iintro H; iexact H
  ihave #Hutf8 : isPkgInit (PROP := IProp GF) pkg_id.unicode.utf8 $$ []
  · iPkgInit
  wp_auto
  repeat' (first
    | wp_if_destruct
    | wp_auto
    | (simp only [strconv.lowerhex_get, strconv.lowerhex_get', strconv.lowerhex_idx_shr_w8_lo, strconv.lowerhex_idx_shr_w8_hi,
        strconv.lowerhex_idx_and_w8_lo, strconv.lowerhex_idx_and_w8_hi, strconv.lowerhex_idx_and_w32_lo,
        strconv.lowerhex_idx_and_w32_hi, _root_.and_self, ↓reduceIte])
    | (wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
       wp_apply wp_slice_append_undo (V := w8) (t := go.byte) _ _ _ _ _ $$ [$Hb $Hcap $Hsl]
         as %b' ⟨Hb, Hcap, -, Hu⟩
       ihave Hundo := appendEscapedRune.undo_comp $$ Hu Hundo)
    | (wp_apply wp_slice_literal
       isplitr
       ipureintro
       rfl
       iintro %sl ⟨Hsl, -⟩
       wp_auto
       wp_apply wp_slice_append_undo (V := w8) (t := go.byte) _ _ _ _ _ $$ [$Hb $Hcap $Hsl]
         as %b' ⟨Hb, Hcap, -, Hu⟩
       ihave Hundo := appendEscapedRune.undo_comp $$ Hu Hundo)
    | (wp_apply wp_IsPrint as %ip -)
    | (wp_apply wp_ValidRune as %vr %Hvr)
    | (wp_apply wp_AppendRune $$ [$Hb $Hcap] as %b' ⟨%q, Hb, Hcap, Hu⟩
       ihave Hundo := appendEscapedRune.undo_comp $$ Hu Hundo))
  all_goals try (try simp only [List.append_assoc]
                 iapply HΦ; iexists _; iframe; done)
  all_goals (
    ihave HI : (∃ (sv : w64) (b : GoSlice) (q : List w8),
        "s" ∷ s_ptr ↦ sv ∗ "buf" ∷ buf_ptr ↦ b ∗ "Hb" ∷ b ↦* bs ++ q ∗
        "Hcap" ∷ ownSliceCap w8 b (DFrac.own 1) ∗
        "Hundo" ∷ (b ↦* bs ++ q ∗ ownSliceCap w8 b (DFrac.own 1) -∗
          buf ↦* bs ∗ ownSliceCap w8 buf (DFrac.own 1)) : IProp GF) $$ [s buf Hb Hcap Hundo]
    · iexists _, _, _
      iframe
    wp_for HI
    wp_if_destruct
    · repeat' (first
        | wp_auto
        | (simp only [strconv.lowerhex_get, strconv.lowerhex_get', strconv.lowerhex_idx_shr_w8_lo,
            strconv.lowerhex_idx_shr_w8_hi, strconv.lowerhex_idx_and_w8_lo, strconv.lowerhex_idx_and_w8_hi,
            strconv.lowerhex_idx_and_w32_lo, strconv.lowerhex_idx_and_w32_hi, _root_.and_self, ↓reduceIte])
        | (wp_apply wp_slice_literal
           isplitr
           ipureintro
           rfl
           iintro %sl ⟨Hsl, -⟩
           wp_auto
           wp_apply wp_slice_append_undo (V := w8) (t := go.byte) _ _ _ _ _ $$ [$Hb $Hcap $Hsl]
             as %b' ⟨Hb, Hcap, -, Hu⟩
           ihave Hundo := appendEscapedRune.undo_comp $$ Hu Hundo))
      wp_for_post
      iframe
      iexists _, _, _
      try simp only [List.append_assoc]
      iframe
    · try (have hc : ¬ sint.Z (W64 0) ≤ sint.Z sv := fun h => Hif (by rw [decide_eq_true h])
           simp only [decide_eq_false hc, decide_true, ↓reduceIte])
      try wp_auto
      try simp only [List.append_assoc]
      iapply HΦ
      iexists _
      iframe)

end proof

end Perennial
