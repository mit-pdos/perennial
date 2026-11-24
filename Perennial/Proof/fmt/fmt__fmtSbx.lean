/-
The proof of `fmt.(*fmt).fmtSbx`.
-/
module

public import Perennial.Spec.fmt.fmt__fmtSbx
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace fmt

theorem hexDigits_lookup (upper : Bool) (d : Nat) (h : d < 16) :
    (hexDigits upper)[d]? = some (hexNibbleByte upper d) := by
  have : ∀ (u : Bool) (e : Fin 16), (hexDigits u)[e.val]? = some (hexNibbleByte u e.val) := by
    decide
  exact this upper ⟨d, h⟩

theorem hexDigits_index_shr4 (c : w8) : sint.nat (W64 (uint.Z (c >>> W64 4))) = uint.nat c / 16 := by
  word

theorem hexDigits_index_and15 (c : w8) : sint.nat (W64 (uint.Z (c &&& W8 15))) = uint.nat c % 16 := by
  have h : (c &&& W8 15).toNat = c.toNat % 16 := by
    rw [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod _ 4
  have h2 : uint.Z (c &&& W8 15) = uint.Z c % 16 := by
    simp only [uint.Z]; rw [h]; push_cast; rfl
  rw [h2]
  word

theorem bytesHex_take_succ (upper : Bool) (bs : GoString) (n : Nat) (c : w8) (h : bs[n]? = some c) :
    bytesHex upper (bs.take (n + 1)) = bytesHex upper (bs.take n) ++
      [hexNibbleByte upper (uint.nat c / 16), hexNibbleByte upper (uint.nat c % 16)] := by
  rw [List.take_add_one, h]
  simp [bytesHex, List.flatMap_append]

end fmt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

/-- `fmt.fmt.fmtSbx.spec` with the premise that the input has fewer than `2^62` bytes: for a
longer one, `width := 2 * length` overflows to a negative `int` and Go writes nothing. -/
theorem fmt.fmt.fmtSbx.wp_proof_of_lt :
    ∀ (f b : Loc) (F : fmtFlags) (wid prec : w64) (bs s : GoString) (sl : GoSlice) (ys : GoString)
      (q : DFrac) (upper : Bool),
      F.precPresent' = false → F.widPresent' = false → F.sharp' = false → F.space' = false →
      (if sl = slice.nil then s else ys).length < 2 ^ 62 →
      {{ fmtOwn (GF := GF) f b F wid prec ∗ bufferOwn b bs ∗ sl ↦*{q} ys }}
        (App (App (App (Val (f @!! go.GoType.PointerType fmt.fmt.ty @!! go!"fmtSbx")) (Val #s)) (Val #sl))
          (Val #(hexDigits upper)))
      {{ RET #(); fmtOwn f b F wid prec ∗
          bufferOwn b (bs ++ bytesHex upper (if sl = slice.nil then s else ys)) ∗ sl ↦*{q} ys }} :=
    fun f b F wid prec bs s sl ys q upper hp hw hs hsp hshort => by
  rcases F with ⟨wp', pp', mi, pl, sh, sp, ze, pv, sv⟩
  simp only at hp hw hs hsp
  subst hp hw hs hsp
  wp_start as ⟨Hf, Hb, Hsl⟩
  unfold fmtOwn
  icases Hf with ⟨Hfb, Hff, Hfw, Hfp⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  wp_auto
  wp_join iprop(length_ptr ↦ W64 (if sl = slice.nil then s else ys).length ∗ s_ptr ↦ s)
    with [length s] as ⟨length, s⟩
  · wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hslen
    wp_join_done
  · rw [ite_eq_right Hif, show sl.len = W64 ys.length by word]
    iframe
  unfold bufferOwn
  icases Hb with ⟨%bsl, Hbp, Hbs, Hbcap⟩
  generalize hd : (if sl = slice.nil then s else ys) = data at hshort ⊢
  wp_if_destruct
  · have hL : 0 < data.length := by word
    ihave IH : iprop(∃ (n : w64) (cv : w8) (bl : GoSlice),
        "i" ∷ i_ptr ↦ n ∗
        "c" ∷ c_ptr ↦ cv ∗
        "buf" ∷ buf_ptr ↦ bl ∗
        "Hbs" ∷ bl ↦* (bs ++ bytesHex upper (data.take (sint.nat n))) ∗
        "Hbcap" ∷ ownSliceCap w8 bl (DFrac.own 1) ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (data.length : Int)⌝) $$ [i c buf Hbs Hbcap]
    · iexists _, _, _
      rw [show sint.nat (W64 0) = 0 by rfl, List.take_zero]
      simp only [bytesHex, List.flatMap_nil, List.append_nil]
      iframe
      ipureintro
      exact ⟨by word, by word⟩
    wp_for IH
    wp_if_destruct
    · have Hlt : sint.nat n < data.length := by word
      obtain ⟨cy, Hcy⟩ : ∃ c, data[sint.nat n]? = some c := ⟨_, List.getElem?_eq_getElem Hlt⟩
      wp_join iprop(c_ptr ↦ cy ∗ b_ptr ↦ sl ∗ s_ptr ↦ s ∗ sl ↦*{q} ys ∗ i_ptr ↦ n)
        with [c b s Hsl i] as ⟨c, b, s, Hsl, i⟩
      · rw [ite_eq_left rfl] at hd
        subst hd
        simp only [Hn.1, ↓reduceIte, Hcy]
        wp_auto
        wp_join_done
      · rw [ite_eq_right Hif] at hd
        subst hd
        simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len by word]
        wp_apply wp_load_slice_index sl (sint.Z n) ys q cy Hn.1 $$ [Hsl] as Hsl
        · iframe; ipureintro; exact Hcy
        wp_join_done
      simp only [show (0 : Int) ≤ sint.Z (W64 (uint.Z (cy >>> W64 4))) by word, ↓reduceIte,
        hexDigits_index_shr4, hexDigits_lookup upper (uint.nat cy / 16) (by word)]
      wp_auto
      simp only [show (0 : Int) ≤ sint.Z (W64 (uint.Z (cy &&& W8 15))) by word, ↓reduceIte,
        hexDigits_index_and15, hexDigits_lookup upper (uint.nat cy % 16) (by word)]
      wp_apply wp_slice_literal (V := w8) (t := go.byte)
        [hexNibbleByte upper (uint.nat cy / 16), hexNibbleByte upper (uint.nat cy % 16)]
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      wp_apply wp_slice_append (V := w8) bl (bs ++ bytesHex upper (data.take (sint.nat n))) _
        [hexNibbleByte upper (uint.nat cy / 16), hexNibbleByte upper (uint.nat cy % 16)] (DFrac.own 1)
        $$ [Hbs Hbcap Hsl2] as %bl' ⟨Hbs, Hbcap, -⟩
      · iframe
      wp_for_post
      iframe
      iexists (n + W64 1), cy, bl'
      iframe
      isplitl
      · iExactEq Hbs
        rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word,
          bytesHex_take_succ upper data (sint.nat n) cy Hcy, List.append_assoc]
      · ipureintro
        constructor <;> word
    · rw [show sint.nat n = data.length by word, List.take_length]
      iapply HΦ
      iframe
  · obtain rfl : data = [] := List.eq_nil_of_length_eq_zero (by word)
    iapply HΦ
    simp only [bytesHex, List.flatMap_nil, List.append_nil]
    iframe

end proof

end Perennial
