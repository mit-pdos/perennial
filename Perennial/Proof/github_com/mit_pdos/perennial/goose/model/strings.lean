/-
Port of `new/proof/github_com/mit_pdos/perennial/goose/model/strings.v`: specs
for the Go model of string/byte-slice conversions
(`github.com/mit-pdos/perennial/goose/model/strings`), used by
`Perennial/Golang/Theory/String.lean`.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Golang.Theory.Pre
import Perennial.Golang.Defn.String
import Perennial.Code.github_com.mit_pdos.perennial.goose.model.strings
import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.model.strings

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.mit_pdos.perennial.goose.model.strings

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : go.StringSemantics]
variable {s : Stuckness} {E : CoPset}

theorem wp_string_len (str : go_string) {t : go.type} [t ↓u go.string] :
    {{ (True : IProp GF) }}
      (App (Val #(functions go.len [t])) (Val #str)) @ s; E
    {{ RET #(W64 str.length); ⌜str.length < 2 ^ 63⌝ }} := by
  wp_start
  by_cases h : str.length < 2 ^ 63
  · rw [ite_eq_left h]
    wp_pures
    iapply HΦ
    ipureintro; exact h
  · rw [ite_eq_right h]
    iapply wp_AngelicExit

theorem wp_StringToByteSlice (str : go_string) :
    {{ (True : IProp GF) }}
      (App (Val (@! StringToByteSlice)) (Val #str)) @ s; E
    {{ (sl : slice.t), RET #sl; sl ↦* str ∗ own_slice_cap w8 sl (DFrac.own 1) }} := by
  wp_start
  wp_auto
  ihave H : (∃ (i : w64) (a : slice.t),
      "i" ∷ i_ptr ↦ i ∗
      "a" ∷ a_ptr ↦ a ∗
      "Ha" ∷ a ↦* str.take (sint.nat i) ∗
      "Ha_cap" ∷ own_slice_cap w8 a (DFrac.own 1) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ str.length⌝ : IProp GF) $$ [a i]
  · iexists (W64 0)
    iexists (zero_val slice.t)
    have h0 : sint.nat (W64 0) = 0 := rfl
    rw [h0, List.take_zero]
    iframe a i
    isplitl []
    · iapply own_slice_nil
    isplitl []
    · iapply own_slice_cap_nil
    · ipureintro; word
  wp_for H
  wp_apply wp_string_len with %Hoverflow
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z (W64 str.length) := by
      rcases Decidable.em (sint.Z i < sint.Z (W64 str.length)) with h | h
      · exact h
      · rw [decide_eq_false h] at Hif; exact absurd Hif false_neq_true
    have hc : sint.nat i < str.length := by word
    obtain ⟨c, Hc_lookup⟩ : ∃ c, str[sint.nat i]? = some c := ⟨_, List.getElem?_eq_getElem hc⟩
    simp only [Hc_lookup]
    wp_pure
    wp_pure
    wp_pure
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte)))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w8) (t := go.byte) [c]
    wp_auto
    have hsz : go.array_literal_size [KeyedElement none (ElementExpression go.byte #c)] = 1 := rfl
    rw [hsz]
    isplitl []
    · ipureintro; rfl
    iintro %sl_ptr ⟨Hsl, _⟩
    wp_auto
    wp_apply wp_slice_append (V := w8) (t := go.byte) a _ _ [c] (DFrac.own 1) $$ [Ha Ha_cap Hsl]
      with %s' ⟨Ha, Ha_cap, _⟩
    · iframe Ha Ha_cap Hsl
    wp_for_post
    iframe
    iexists (i + W64 1)
    iexists s'
    have hn : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    rw [hn, List.take_add_one, Hc_lookup]
    simp only [Option.toList_some]
    iframe
    ipureintro; word
  · have hP : ¬ sint.Z i < sint.Z (W64 str.length) := fun h => Hif (by rw [decide_eq_true h])
    rw [decide_eq_false hP]
    simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    have hi : sint.nat i = str.length := by word
    rw [hi, List.take_length]
    iframe Ha Ha_cap

theorem wp_ByteSliceToString (sl : slice.t) (str : List w8) (dq : DFrac) :
    {{ (sl ↦*{dq} str : IProp GF) }}
      (App (Val (@! ByteSliceToString)) (Val #sl)) @ s; E
    {{ RET #str; sl ↦*{dq} str }} := by
  wp_start as Hsl
  wp_auto
  ihave %Hlen := own_slice_len _ _ _ $$ Hsl
  ihave H : (∃ (i : w64) (c : w8),
      "i" ∷ i_ptr ↦ i ∗
      "c" ∷ c_ptr ↦ c ∗
      "s" ∷ s_ptr ↦ str.take (sint.nat i) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ str.length⌝ : IProp GF) $$ [s c i]
  · iexists (W64 0)
    iexists (zero_val w8)
    have h0 : sint.nat (W64 0) = 0 := rfl
    rw [h0, List.take_zero]
    iframe
    ipureintro; word
  wp_for H
  wp_if_destruct
  · rw [ite_eq_left ⟨Hi.1, Hif⟩]
    have hc : sint.nat i < str.length := by word
    obtain ⟨c', Hc_lookup⟩ : ∃ c, str[sint.nat i]? = some c := ⟨_, List.getElem?_eq_getElem hc⟩
    wp_apply wp_load_slice_index (V := w8) (t := go.byte) sl (sint.Z i) str dq c' Hi.1 $$ [Hsl]
      with Hsl
    · isplitl [Hsl]
      · iexact Hsl
      · ipureintro; exact Hc_lookup
    wp_for_post
    iframe
    iexists (i + W64 1)
    iexists c'
    have hn : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    rw [hn, List.take_add_one, Hc_lookup]
    simp only [Option.toList_some]
    iframe
    ipureintro; word
  · have hi : sint.nat i = str.length := by word
    rw [hi, List.take_length]
    iapply HΦ $$ Hsl

end wps

end github_com.mit_pdos.perennial.goose.model.strings

end Perennial
