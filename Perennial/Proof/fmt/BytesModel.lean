/-
Specs of the helpers of the model of `fmt` (`Perennial/TrustedCode/fmt.lean`) that format a `[]byte`
argument: `hexNibble`, `quoteByte`, `quoteBytes` and `formatSlice`.
-/
module

public import Perennial.Proof.fmt.Args
public import Perennial.Proof.fmt.SprintfModel

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace fmt

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

/-- The helper `fmt.hexNibble`: the hexadecimal digit of `d` (below 16). -/
theorem wp_hexNibble (d : w8) (upper : Bool) (hd : uint.nat d < 16) :
    {{ (True : IProp GF) }}
      (App (App (Val hexNibble) (Val #d)) (Val #upper))
    {{ (r : w8), RET #r; ⌜r = hexNibbleByte upper (uint.nat d)⌝ }} := by
  iintro %Φ - HΦ
  unfold hexNibble
  wp_auto
  wp_if_destruct
  · iapply HΦ; ipureintro
    unfold hexNibbleByte
    rw [if_pos (by word)]
    word
  wp_if_destruct
  · iapply HΦ; ipureintro
    unfold hexNibbleByte
    rw [if_neg (by word)]
    try simp only [Bool.false_eq_true, ↓reduceIte]
    word
  · iapply HΦ; ipureintro
    unfold hexNibbleByte
    rw [if_neg (by word)]
    try simp only [Bool.false_eq_true, ↓reduceIte]
    word

omit package_sem in
/-- A `[]byte` composite literal of one byte. -/
theorem wp_bytesLit1 (a : w8) :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
        (Val (LiteralValueV [KeyedElement none (ElementExpression go.byte #a)])))
    {{ (sl : GoSlice), RET #sl; sl ↦* [a] }} := by
  iintro %Φ - HΦ
  iapply wp_slice_literal (V := w8) (t := go.byte) [a]
  wp_auto
  rw [show go.arrayLiteralSize [KeyedElement none (ElementExpression go.byte #a)] = 1 from rfl]
  isplitl []
  · ipureintro; rfl
  iintro %sl_ptr ⟨Hsl, -⟩
  iapply HΦ; iexact Hsl

omit package_sem in
/-- A `[]byte` composite literal of two bytes. -/
theorem wp_bytesLit2 (a b : w8) :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
        (Val (LiteralValueV [KeyedElement none (ElementExpression go.byte #a),
          KeyedElement none (ElementExpression go.byte #b)])))
    {{ (sl : GoSlice), RET #sl; sl ↦* [a, b] }} := by
  iintro %Φ - HΦ
  iapply wp_slice_literal (V := w8) (t := go.byte) [a, b]
  wp_auto
  rw [show go.arrayLiteralSize [KeyedElement none (ElementExpression go.byte #a),
    KeyedElement none (ElementExpression go.byte #b)] = 2 from rfl]
  isplitl []
  · ipureintro; rfl
  iintro %sl_ptr ⟨Hsl, -⟩
  iapply HΦ; iexact Hsl

omit package_sem in
/-- A `[]byte` composite literal of four bytes. -/
theorem wp_bytesLit4 (a b c d : w8) :
    {{ (True : IProp GF) }}
      (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
        (Val (LiteralValueV [KeyedElement none (ElementExpression go.byte #a),
          KeyedElement none (ElementExpression go.byte #b),
          KeyedElement none (ElementExpression go.byte #c),
          KeyedElement none (ElementExpression go.byte #d)])))
    {{ (sl : GoSlice), RET #sl; sl ↦* [a, b, c, d] }} := by
  iintro %Φ - HΦ
  iapply wp_slice_literal (V := w8) (t := go.byte) [a, b, c, d]
  wp_auto
  rw [show go.arrayLiteralSize [KeyedElement none (ElementExpression go.byte #a),
    KeyedElement none (ElementExpression go.byte #b),
    KeyedElement none (ElementExpression go.byte #c),
    KeyedElement none (ElementExpression go.byte #d)] = 4 from rfl]
  isplitl []
  · ipureintro; rfl
  iintro %sl_ptr ⟨Hsl, -⟩
  iapply HΦ; iexact Hsl

/-- `quotedByte` of a control byte without a short escape (or `0x7F`): `\xNN`. -/
theorem quotedByte_default (c r1 r2 : w8)
    (hr1 : r1 = hexNibbleByte false (uint.nat (c / W8 16)))
    (hr2 : r2 = hexNibbleByte false (uint.nat (c % W8 16)))
    (h34 : c ≠ W8 34) (h92 : c ≠ W8 92) (h2 : ¬(32 ≤ uint.nat c ∧ uint.nat c ≤ 126))
    (h7 : c ≠ W8 7) (h8 : c ≠ W8 8) (h12 : c ≠ W8 12) (h10 : c ≠ W8 10) (h13 : c ≠ W8 13)
    (h9 : c ≠ W8 9) (h11 : c ≠ W8 11) :
    [W8 92, W8 120, r1, r2] = quotedByte c := by
  unfold quotedByte
  rw [if_neg (by rintro (h | h) <;> contradiction), if_neg h2, if_neg h7, if_neg h8, if_neg h12, if_neg h10, if_neg h13,
    if_neg h9, if_neg h11, hr1, hr2,
    show uint.nat (c / W8 16) = uint.nat c / 16 by word,
    show uint.nat (c % W8 16) = uint.nat c % 16 by word]

set_option maxHeartbeats 4000000 in
/-- The helper `fmt.quoteByte`: the byte `c` as `strconv.Quote` writes it (`quotedByte`). -/
theorem wp_quoteByte (c : w8) :
    {{ (True : IProp GF) }}
      (App (Val quoteByte) (Val #c))
    {{ (s : GoString), RET #s; ⌜s = quotedByte c⌝ }} := by
  iintro %Φ - HΦ
  unfold quoteByte
  wp_auto
  repeat' (first | wp_if_destruct | wp_auto)
  all_goals first
    | (iapply HΦ; ipureintro; unfold quotedByte; simp_all; done)
    | skip
  all_goals (try (wp_apply (wp_hexNibble _ false (by word)) as %r1 %Hr1))
  all_goals (try wp_auto)
  all_goals (try (wp_apply (wp_hexNibble _ false (by word)) as %r2 %Hr2))
  all_goals (try wp_auto)
  all_goals (first
    | wp_apply wp_bytesLit1 as %sl Hsl
    | wp_apply wp_bytesLit2 as %sl Hsl
    | wp_apply wp_bytesLit4 as %sl Hsl)
  all_goals (wp_apply wp_bytes_to_string $$ Hsl as -)
  all_goals (try wp_auto)
  all_goals (iapply HΦ; ipureintro)
  all_goals first
    | (unfold quotedByte; simp; done)
    | (refine quotedByte_default c _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
         first | assumption | (rintro ⟨h, h'⟩; word))
    | (have hq : ¬(c = W8 34 ∨ c = W8 92) := by rintro (h | h) <;> contradiction
       have hp : 32 ≤ uint.nat c ∧ uint.nat c ≤ 126 := by constructor <;> word
       unfold quotedByte
       rw [if_neg hq, if_pos hp])

set_option maxHeartbeats 2000000 in
/-- The helper `fmt.quoteBytes`: `quoteASCII bs` and `true` when every byte is ASCII, `false` when one
is not; it reads the bytes and gives them back. -/
theorem wp_quoteBytes (sl : GoSlice) (bs : GoString) (dq : DFrac) :
    {{ (sl ↦*{dq} bs : IProp GF) }}
      (App (Val quoteBytes) (Val #sl))
    {{ (s : GoString) (ok : Bool), RET (PairV #s #ok); sl ↦*{dq} bs ∗
        ⌜(ok = true ↔ ∀ b ∈ bs, uint.nat b < 128) ∧ (ok = true → s = quoteASCII bs)⌝ }} := by
  iintro %Φ Hsl HΦ
  unfold quoteBytes
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave IH : iprop(∃ (i : w64) (o : GoString) (cv : w8),
      "i" ∷ i_ptr ↦ i ∗ "out" ∷ out_ptr ↦ o ∗ "c" ∷ c_ptr ↦ cv ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ (bs.length : Int)⌝ ∗
      "%Ho" ∷ ⌜o = W8 34 :: (bs.take (sint.nat i)).flatMap quotedByte⌝ ∗
      "%Ha" ∷ ⌜∀ b ∈ bs.take (sint.nat i), uint.nat b < 128⌝) $$ [i out c]
  · iexists _, _, _
    iframe
    ipureintro
    rw [show sint.nat (W64 0) = 0 from rfl]
    exact ⟨⟨by word, by word⟩, by simp, by simp⟩
  wp_for IH
  split
  · rename_i Hif
    replace Hif := of_decide_eq_true Hif
    have Hlt : sint.nat i < bs.length := by word
    obtain ⟨c, Hc⟩ : ∃ c, bs[sint.nat i]? = some c := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hsucc : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    wp_auto
    rw [ite_eq_left ⟨Hi.1, Hif⟩]
    wp_apply wp_load_slice_index sl (sint.Z i) bs dq c Hi.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hc
    wp_if_destruct
    · -- a byte from `0x80`: not ASCII
      wp_for_post
      iapply HΦ
      iframe
      ipureintro
      refine ⟨?_, fun h => nomatch h⟩
      constructor
      · intro h; cases h
      · intro h
        have := h c (List.mem_of_getElem? Hc)
        word
    · wp_apply wp_quoteByte as %q %Hq
      try wp_auto
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ?_, ?_⟩
      · rw [Ho, Hsucc, List.take_add_one, Hc, Hq]; simp
      · rw [Hsucc, List.take_add_one, Hc]
        intro b hb
        simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · exact Ha b hb
        · word
  · rename_i Hif
    have Hnot : ¬ (sint.Z i < sint.Z sl.len) := by simpa using Hif
    have Hend : sint.nat i = bs.length := by word
    rw [Hend, List.take_length] at Ho Ha
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    refine ⟨⟨fun _ => Ha, fun _ => rfl⟩, fun _ => ?_⟩
    rw [Ho]; simp [quoteASCII]

set_option maxHeartbeats 2000000 in
/-- The helper `fmt.hexBytes`: `bytesHex upper bs`; it reads the bytes and gives them back. -/
theorem wp_hexBytes (sl : GoSlice) (bs : GoString) (dq : DFrac) (upper : Bool) :
    {{ (sl ↦*{dq} bs : IProp GF) }}
      (App (App (Val hexBytes) (Val #sl)) (Val #upper))
    {{ (s : GoString), RET #s; sl ↦*{dq} bs ∗ ⌜s = bytesHex upper bs⌝ }} := by
  iintro %Φ Hsl HΦ
  unfold hexBytes
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave IH : iprop(∃ (i : w64) (o : GoString) (cv : w8),
      "i" ∷ i_ptr ↦ i ∗ "out" ∷ out_ptr ↦ o ∗ "c" ∷ c_ptr ↦ cv ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ (bs.length : Int)⌝ ∗
      "%Ho" ∷ ⌜o = bytesHex upper (bs.take (sint.nat i))⌝) $$ [i out c]
  · iexists _, _, _
    iframe
    ipureintro
    rw [show sint.nat (W64 0) = 0 from rfl]
    exact ⟨⟨by word, by word⟩, by simp [bytesHex]; rfl⟩
  wp_for IH
  split
  · rename_i Hif
    replace Hif := of_decide_eq_true Hif
    have Hlt : sint.nat i < bs.length := by word
    obtain ⟨c, Hc⟩ : ∃ c, bs[sint.nat i]? = some c := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hsucc : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    wp_auto
    rw [ite_eq_left ⟨Hi.1, Hif⟩]
    wp_apply wp_load_slice_index sl (sint.Z i) bs dq c Hi.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hc
    wp_apply (wp_hexNibble _ upper (by word)) as %r1 %Hr1
    try wp_auto
    wp_apply (wp_hexNibble _ upper (by word)) as %r2 %Hr2
    try wp_auto
    wp_apply wp_bytesLit2 as %bsl Hb
    wp_apply wp_bytes_to_string $$ Hb as -
    try wp_auto
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    ipureintro
    refine ⟨⟨by word, by word⟩, ?_⟩
    rw [Ho, Hsucc, List.take_add_one, Hc, Hr1, Hr2]
    simp only [bytesHex, Option.toList_some, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    rw [show uint.nat (c / W8 16) = uint.nat c / 16 by word,
      show uint.nat (c % W8 16) = uint.nat c % 16 by word]
  · rename_i Hif
    have Hnot : ¬ (sint.Z i < sint.Z sl.len) := by simpa using Hif
    have Hend : sint.nat i = bs.length := by word
    rw [Hend, List.take_length] at Ho
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    exact Ho

set_option maxHeartbeats 2000000 in
/-- The helper `fmt.decBytes`: `bytesDec bs`; it reads the bytes and gives them back. -/
theorem wp_decBytes (sl : GoSlice) (bs : GoString) (dq : DFrac) :
    {{ (sl ↦*{dq} bs : IProp GF) }}
      (App (Val decBytes) (Val #sl))
    {{ (s : GoString), RET #s; sl ↦*{dq} bs ∗ ⌜s = bytesDec bs⌝ }} := by
  iintro %Φ Hsl HΦ
  unfold decBytes
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave IH : iprop(∃ (i : w64) (o : GoString) (kv : w64) (cv : w8),
      "i" ∷ i_ptr ↦ i ∗ "out" ∷ out_ptr ↦ o ∗ "k" ∷ k_ptr ↦ kv ∗ "c" ∷ c_ptr ↦ cv ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ (bs.length : Int)⌝ ∗
      "%Ho" ∷ ⌜o = W8 91 :: ((bs.take (sint.nat i)).mapIdx fun k c =>
        (if k = 0 then [] else [W8 32]) ++ decimalPad 0 (uint.Z c)).flatten⌝) $$ [i out k c]
  · iexists _, _, _, _
    iframe
    ipureintro
    rw [show sint.nat (W64 0) = 0 from rfl]
    exact ⟨⟨by word, by word⟩, by simp⟩
  wp_for IH
  split
  · rename_i Hif
    replace Hif := of_decide_eq_true Hif
    have Hlt : sint.nat i < bs.length := by word
    obtain ⟨c, Hc⟩ : ∃ c, bs[sint.nat i]? = some c := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hsucc : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    have Htk : (bs.take (sint.nat i)).length = sint.nat i := by simp; omega
    have Hstep : ∀ sep : GoString, (sep = if sint.nat i = 0 then [] else [W8 32]) →
        (W8 91 :: ((bs.take (sint.nat i)).mapIdx fun k c =>
          (if k = 0 then [] else [W8 32]) ++ decimalPad 0 (uint.Z c)).flatten) ++ sep ++
            decimalPad 0 (uint.Z c) =
        W8 91 :: ((bs.take (sint.nat (i + W64 1))).mapIdx fun k c =>
          (if k = 0 then [] else [W8 32]) ++ decimalPad 0 (uint.Z c)).flatten := by
      intro sep hsep
      rw [Hsucc, List.take_add_one, Hc, Option.toList_some, List.mapIdx_append, Htk]
      simp [hsep]
    wp_auto
    rw [ite_eq_left ⟨Hi.1, Hif⟩]
    wp_apply wp_load_slice_index sl (sint.Z i) bs dq c Hi.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hc
    try wp_auto
    wp_if_destruct
    · -- not the first byte: a space
      try wp_auto
      wp_apply (wp_formatInt false _ (W64 0) (fun h => nomatch h) ⟨by word, by word⟩)
      try wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ?_⟩
      have hs : ([W8 32] : GoString) = if sint.nat i = 0 then [] else [W8 32] := by
        rw [if_neg (by word)]
      rw [← Hstep [W8 32] hs, Ho]
      have hsv : signedValue false (W64 (uint.Z c)) = uint.Z c := by
        unfold signedValue; simp only [Bool.false_eq_true, ↓reduceIte]; word
      rw [hsv]
      rfl
    · wp_apply (wp_formatInt false _ (W64 0) (fun h => nomatch h) ⟨by word, by word⟩)
      try wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ?_⟩
      have hs : ([] : GoString) = if sint.nat i = 0 then [] else [W8 32] := by
        rw [if_pos (by word)]
      rw [← Hstep [] hs, Ho]
      have hsv : signedValue false (W64 (uint.Z c)) = uint.Z c := by
        unfold signedValue; simp only [Bool.false_eq_true, ↓reduceIte]; word
      rw [hsv, List.append_nil]
  · rename_i Hif
    have Hnot : ¬ (sint.Z i < sint.Z sl.len) := by simpa using Hif
    have Hend : sint.nat i = bs.length := by word
    rw [Hend, List.take_length] at Ho
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    rw [Ho]; simp [bytesDec]

set_option maxHeartbeats 2000000 in
/-- The helper `fmt.joinStrings`: `stringsJoin ss`; it reads the strings and gives them back. -/
theorem wp_joinStrings (sl : GoSlice) (ss : List GoString) (dq : DFrac) :
    {{ (sl ↦*{dq} ss : IProp GF) }}
      (App (Val joinStrings) (Val #sl))
    {{ (s : GoString), RET #s; sl ↦*{dq} ss ∗ ⌜s = stringsJoin ss⌝ }} := by
  iintro %Φ Hsl HΦ
  unfold joinStrings
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave IH : iprop(∃ (i : w64) (o : GoString) (kv : w64) (sv : GoString),
      "i" ∷ i_ptr ↦ i ∗ "out" ∷ out_ptr ↦ o ∗ "k" ∷ k_ptr ↦ kv ∗ "s" ∷ s_ptr ↦ sv ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ (ss.length : Int)⌝ ∗
      "%Ho" ∷ ⌜o = W8 91 :: ((ss.take (sint.nat i)).mapIdx fun k s =>
        (if k = 0 then [] else [W8 32]) ++ s).flatten⌝) $$ [i out k s]
  · iexists _, _, _, _
    iframe
    ipureintro
    rw [show sint.nat (W64 0) = 0 from rfl]
    exact ⟨⟨by word, by word⟩, by simp⟩
  wp_for IH
  split
  · rename_i Hif
    replace Hif := of_decide_eq_true Hif
    have Hlt : sint.nat i < ss.length := by word
    obtain ⟨c, Hc⟩ : ∃ c, ss[sint.nat i]? = some c := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hsucc : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    have Htk : (ss.take (sint.nat i)).length = sint.nat i := by simp; omega
    have Hstep : ∀ sep : GoString, (sep = if sint.nat i = 0 then [] else [W8 32]) →
        (W8 91 :: ((ss.take (sint.nat i)).mapIdx fun k s =>
          (if k = 0 then [] else [W8 32]) ++ s).flatten) ++ sep ++ c =
        W8 91 :: ((ss.take (sint.nat (i + W64 1))).mapIdx fun k s =>
          (if k = 0 then [] else [W8 32]) ++ s).flatten := by
      intro sep hsep
      rw [Hsucc, List.take_add_one, Hc, Option.toList_some, List.mapIdx_append, Htk]
      simp [hsep]
    wp_auto
    rw [ite_eq_left ⟨Hi.1, Hif⟩]
    wp_apply wp_load_slice_index sl (sint.Z i) ss dq c Hi.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hc
    try wp_auto
    wp_if_destruct
    · -- not the first string: a space
      try wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ?_⟩
      have hs : ([W8 32] : GoString) = if sint.nat i = 0 then [] else [W8 32] := by
        rw [if_neg (by word)]
      rw [← Hstep [W8 32] hs, Ho]
      rfl
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ?_⟩
      have hs : ([] : GoString) = if sint.nat i = 0 then [] else [W8 32] := by
        rw [if_pos (by word)]
      rw [← Hstep [] hs, Ho, List.append_nil]
  · rename_i Hif
    have Hnot : ¬ (sint.Z i < sint.Z sl.len) := by simpa using Hif
    have Hend : sint.nat i = ss.length := by word
    rw [Hend, List.take_length] at Ho
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    rw [Ho]; simp [stringsJoin]

set_option maxHeartbeats 8000000 in
/-- The helper `fmt.formatSlice`, at an argument whose contents are lent (`B`) when it is a `[]byte`
or a `[]string` under a verb of `byteVerbs`: it formats the directive (`SprintfOutB`'s `bytes*` and
`strs`) when the model does, reading the lent bytes or strings and giving them back; otherwise it
formats nothing, and the directive is neither `BytesSimple` nor `StringsSimple`. -/
theorem wp_formatSliceB (B : GoInterface → Option Lent) (dqb : DFrac) (format : GoString)
    (i : w64) (x : GoInterface) (Hi : 0 ≤ sint.Z i ∧ sint.Z i < (format.length : Int))
    (Hx : ∀ c, (format.drop (sint.nat i + 1)).head? = some c → c ∈ byteVerbs →
      ∀ ii, x = interface.ok ii → (ii.ty = go.SliceType go.byte ∨ ii.ty = go.SliceType go.string) →
        (B x).isSome) :
    {{ bytesArgOwn (GF := GF) dqb B x }}
      (App (App (App (Val formatSlice) (Val #format)) (Val #i)) (Val #x))
    {{ (s : GoString) (next : w64) (ok : Bool), RET (PairV (PairV #s #next) #ok);
        bytesArgOwn dqb B x ∗
        ⌜ok = true → sint.Z next = sint.Z i + 2 ∧ sint.Z i < sint.Z next ∧
          sint.Z next ≤ (format.length : Int) ∧
          (∀ args r, SprintfOutB B (format.drop (sint.nat next)) args r →
            SprintfOutB B (W8 37 :: format.drop (sint.nat i + 1)) (x :: args) (s ++ r)) ∧
          AuxStep format (sint.nat i) (sint.nat next)⌝ ∗
        ⌜ok = false → ∀ args, ¬ BytesSimple B (format.drop (sint.nat i + 1)) (x :: args) ∧
          ¬ StringsSimple B (format.drop (sint.nat i + 1)) (x :: args)⌝ }} := by
  iintro %Φ Hown HΦ
  unfold formatSlice
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hflen
  wp_if_destruct
  · iapply HΦ
    iframe
    have hdn : format.drop (sint.nat i + 1) = [] := List.drop_eq_nil_of_le (by word)
    isplitl []
    · ipureintro; intro h; cases h
    · ipureintro; intro _ args
      rw [hdn]; simp [BytesSimple, StringsSimple]
  have Hlt : sint.nat i + 1 < format.length := by word
  obtain ⟨c, Hc, Hdrop⟩ : ∃ c, format[sint.nat i + 1]? = some c ∧
      format.drop (sint.nat i + 1) = c :: format.drop (sint.nat i + 2) :=
    ⟨_, List.getElem?_eq_getElem Hlt, List.drop_eq_getElem_cons Hlt⟩
  have Hidx : format[sint.nat (i + W64 1)]? = some c := by
    rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]; exact Hc
  rw [if_pos (show 0 ≤ sint.Z (i + W64 1) by word), Hidx]
  wp_auto
  have Hxc := Hx c (by rw [Hdrop]; rfl)
  have Hdrop2 : sint.nat (i + W64 2) = sint.nat i + 2 := by word
  have Hnext : format.drop (sint.nat i + 1) = c :: format.drop (sint.nat (i + W64 2)) := by
    rw [Hdrop2]; exact Hdrop
  by_cases hc : c ∈ byteVerbs
  rotate_left
  · -- not a byte verb: nothing formatted
    repeat' (first | wp_if_destruct | wp_auto)
    all_goals first
      | (exfalso; simp_all [byteVerbs]; done)
      | (iapply HΦ; iframe
         isplitl []
         · ipureintro; intro h; cases h
         ipureintro; intro _ args
         rw [Hdrop]
         constructor
         · rintro ⟨ii, bs, -, -, -, hcs⟩
           apply hc
           simp only [byteVerbs, List.mem_cons, List.not_mem_nil, or_false]
           rcases hcs with h | h | h | h | h | ⟨h, -⟩ <;> simp [h]
         · rintro ⟨ii, ss, -, -, -, hcs⟩
           apply hc
           simp only [byteVerbs, List.mem_cons, List.not_mem_nil, or_false]
           rcases hcs with h | h <;> simp [h])
  cases x with
  | nil =>
    repeat' (first | wp_if_destruct | wp_auto)
    all_goals first
      | (exfalso; simp_all [byteVerbs]; done)
      | (iapply HΦ; iframe
         isplitl []
         · ipureintro; intro h; cases h
         ipureintro; intro _ args
         rw [Hdrop]
         constructor
         · rintro ⟨ii, bs, h, -⟩
           cases h
         · rintro ⟨ii, ss, h, -⟩
           cases h)
  | ok ii =>
    have hbs_ne : go.SliceType go.byte ≠ go.SliceType go.string := by
      simp [go.byte, go.string, go.uint8]
    by_cases hts : ii.ty = go.SliceType go.string
    · -- a `[]string`: lent
      have hty : ii.ty ≠ go.SliceType go.byte := fun h => hbs_ne (h ▸ hts)
      obtain ⟨L, hL⟩ := Option.isSome_iff_exists.mp (Hxc hc ii rfl (.inr hts))
      cases L with
      | bytes bs =>
        icases (bytesArgOwn_some (dq := dqb) hL).1 $$ Hown with ⟨%ii', %sl, %Hp, -⟩
        obtain ⟨hii, hty', -⟩ := Hp
        cases hii
        exact absurd hty' hty
      | strings ss =>
      icases (bytesArgOwn_strings (dq := dqb) hL).1 $$ Hown with ⟨%ii', %sl, %Hp, Hsl⟩
      obtain ⟨hii, -, hv⟩ := Hp
      cases hii
      ihave Hback : iprop(sl ↦*{dqb} ss -∗ bytesArgOwn dqb B (interface.ok ii)) $$ []
      · iintro Hsl
        iapply (bytesArgOwn_strings (dq := dqb) hL).2
        iexists ii, sl
        iframe
        ipureintro; exact ⟨rfl, hts, hv⟩
      by_cases hsv : c = W8 115 ∨ c = W8 118
      · rcases hsv with rfl | rfl
        all_goals
          repeat' (first | wp_if_destruct | wp_auto | simp only [hts, hv, ↓reduceIte, _root_.decide_true])
        all_goals first
          | (exfalso; simp_all; done)
          | skip
        all_goals
          wp_apply (wp_joinStrings sl ss dqb) $$ Hsl as %s ⟨Hsl, %Hs⟩
          try wp_auto
          iapply HΦ
          isplitl [Hback Hsl]
          · iapply Hback; iexact Hsl
          ipureintro
          refine ⟨fun _ => ⟨by word, by word, by word, fun args r hr => ?_,
            auxStep_byteVerb format _ _ _ hc Hnext⟩, fun h => nomatch h⟩
          rw [Hdrop]
          rw [Hdrop2] at hr
          rw [Hs]
          exact SprintfOutB.strs _ ii ss _ args r (by decide) hts hL hr
      · repeat' (first | wp_if_destruct | wp_auto | simp only [hts, hv, ↓reduceIte, _root_.decide_true])
        all_goals first
          | (exfalso; simp_all; done)
          | (iapply HΦ
             isplitl [Hback Hsl]
             · iapply Hback; iexact Hsl
             isplitl []
             · ipureintro; intro h; cases h
             ipureintro; intro _ args
             rw [Hdrop]
             constructor
             · rintro ⟨ii', bs, h, h2, -⟩
               cases h
               exact hty h2
             · rintro ⟨ii', ss', h, -, -, h4⟩
               exact hsv h4)
    by_cases hty : ii.ty = go.SliceType go.byte
    rotate_left
    · repeat' (first | wp_if_destruct | wp_auto | simp only [hty, hts, ↓reduceIte, decide_false])
      all_goals first
        | (exfalso; simp_all [byteVerbs]; done)
        | (iapply HΦ; iframe
           isplitl []
           · ipureintro; intro h; cases h
           ipureintro; intro _ args
           rw [Hdrop]
           constructor
           · rintro ⟨ii', bs, h, h2, -⟩
             cases h
             exact hty h2
           · rintro ⟨ii', ss, h, h2, -⟩
             cases h
             exact hts h2)
    obtain ⟨L, hL⟩ := Option.isSome_iff_exists.mp (Hxc hc ii rfl (.inl hty))
    cases L with
    | strings ss =>
      icases (bytesArgOwn_strings (dq := dqb) hL).1 $$ Hown with ⟨%ii', %sl, %Hp, -⟩
      obtain ⟨hii, hty', -⟩ := Hp
      cases hii
      exact absurd hty' hts
    | bytes bs =>
    have hbs := hL
    icases (bytesArgOwn_some (dq := dqb) hbs).1 $$ Hown with ⟨%ii', %sl, %Hp, Hsl⟩
    obtain ⟨hii, -, hv⟩ := Hp
    cases hii
    ihave Hback : iprop(sl ↦*{dqb} bs -∗ bytesArgOwn dqb B (interface.ok ii)) $$ []
    · iintro Hsl
      iapply (bytesArgOwn_some (dq := dqb) hbs).2
      iexists ii, sl
      iframe
      ipureintro; exact ⟨rfl, hty, hv⟩
    have hc' := hc
    simp only [byteVerbs, List.mem_cons, List.not_mem_nil, _root_.or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl
    · -- `%s`
      repeat' (first | wp_if_destruct | wp_auto | simp only [hty, hts, hv, ↓reduceIte, _root_.decide_true, decide_false])
      all_goals first
        | (exfalso; simp_all; done)
        | skip
      wp_apply wp_bytes_to_string $$ Hsl as Hsl
      try wp_auto
      iapply HΦ
      isplitl [Hback Hsl]
      · iapply Hback; iexact Hsl
      ipureintro
      refine ⟨fun _ => ⟨by word, by word, by word, fun args r hr => ?_,
        auxStep_byteVerb format _ _ _ hc Hnext⟩, fun h => nomatch h⟩
      rw [Hdrop]
      rw [Hdrop2] at hr
      exact SprintfOutB.bytesS ii bs _ args r hty hbs hr
    · -- `%v`
      repeat' (first | wp_if_destruct | wp_auto | simp only [hty, hts, hv, ↓reduceIte, _root_.decide_true, decide_false])
      all_goals first
        | (exfalso; simp_all; done)
        | skip
      wp_apply (wp_decBytes sl bs dqb) $$ Hsl as %s ⟨Hsl, %Hs⟩
      try wp_auto
      iapply HΦ
      isplitl [Hback Hsl]
      · iapply Hback; iexact Hsl
      ipureintro
      refine ⟨fun _ => ⟨by word, by word, by word, fun args r hr => ?_,
        auxStep_byteVerb format _ _ _ hc Hnext⟩, fun h => nomatch h⟩
      rw [Hdrop]
      rw [Hdrop2] at hr
      rw [Hs]
      exact SprintfOutB.bytesV (W8 118) ii bs _ args r (.inl rfl) hty hbs hr
    · -- `%d`
      repeat' (first | wp_if_destruct | wp_auto | simp only [hty, hts, hv, ↓reduceIte, _root_.decide_true, decide_false])
      all_goals first
        | (exfalso; simp_all; done)
        | skip
      wp_apply (wp_decBytes sl bs dqb) $$ Hsl as %s ⟨Hsl, %Hs⟩
      try wp_auto
      iapply HΦ
      isplitl [Hback Hsl]
      · iapply Hback; iexact Hsl
      ipureintro
      refine ⟨fun _ => ⟨by word, by word, by word, fun args r hr => ?_,
        auxStep_byteVerb format _ _ _ hc Hnext⟩, fun h => nomatch h⟩
      rw [Hdrop]
      rw [Hdrop2] at hr
      rw [Hs]
      exact SprintfOutB.bytesV (W8 100) ii bs _ args r (.inr rfl) hty hbs hr
    · -- `%x`
      repeat' (first | wp_if_destruct | wp_auto | simp only [hty, hts, hv, ↓reduceIte, _root_.decide_true, decide_false])
      all_goals first
        | (exfalso; simp_all; done)
        | skip
      wp_apply (wp_hexBytes sl bs dqb _) $$ Hsl as %s ⟨Hsl, %Hs⟩
      try wp_auto
      iapply HΦ
      isplitl [Hback Hsl]
      · iapply Hback; iexact Hsl
      ipureintro
      refine ⟨fun _ => ⟨by word, by word, by word, fun args r hr => ?_,
        auxStep_byteVerb format _ _ _ hc Hnext⟩, fun h => nomatch h⟩
      rw [Hdrop]
      rw [Hdrop2] at hr
      rw [Hs]
      exact SprintfOutB.bytesX false ii bs _ args r hty hbs hr
    · -- `%X`
      repeat' (first | wp_if_destruct | wp_auto | simp only [hty, hts, hv, ↓reduceIte, _root_.decide_true, decide_false])
      all_goals first
        | (exfalso; simp_all; done)
        | skip
      wp_apply (wp_hexBytes sl bs dqb _) $$ Hsl as %s ⟨Hsl, %Hs⟩
      try wp_auto
      iapply HΦ
      isplitl [Hback Hsl]
      · iapply Hback; iexact Hsl
      ipureintro
      refine ⟨fun _ => ⟨by word, by word, by word, fun args r hr => ?_,
        auxStep_byteVerb format _ _ _ hc Hnext⟩, fun h => nomatch h⟩
      rw [Hdrop]
      rw [Hdrop2] at hr
      rw [Hs]
      exact SprintfOutB.bytesX true ii bs _ args r hty hbs hr
    · -- `%q`
      repeat' (first | wp_if_destruct | wp_auto | simp only [hty, hts, hv, ↓reduceIte, _root_.decide_true, decide_false])
      all_goals first
        | (exfalso; simp_all; done)
        | skip
      wp_apply (wp_quoteBytes sl bs dqb) $$ Hsl as %s %okq ⟨Hsl, %Hq⟩
      cases okq
      · -- a byte from `0x80`: not formatted
        repeat' (first | wp_if_destruct | wp_auto)
        iapply HΦ
        isplitl [Hback Hsl]
        · iapply Hback; iexact Hsl
        isplitl []
        · ipureintro; intro h; cases h
        ipureintro; intro _ args
        rw [Hdrop]
        constructor
        · rintro ⟨ii', bs', h1, -, h3, hcs⟩
          cases h1
          rw [hbs] at h3
          cases h3
          rcases hcs with h | h | h | h | h | ⟨-, hasc⟩
          all_goals first
            | (revert h; decide)
            | exact absurd (Hq.1.2 hasc) (by simp)
        · rintro ⟨ii', ss, h1, h2, -⟩
          cases h1
          exact hts h2
      repeat' (first | wp_if_destruct | wp_auto)
      iapply HΦ
      isplitl [Hback Hsl]
      · iapply Hback; iexact Hsl
      ipureintro
      refine ⟨fun _ => ⟨by word, by word, by word, fun args r hr => ?_,
        auxStep_byteVerb format _ _ _ hc Hnext⟩, fun h => nomatch h⟩
      rw [Hdrop]
      rw [Hdrop2] at hr
      rw [Hq.2 rfl]
      exact SprintfOutB.bytesQ ii bs _ args r hty hbs (Hq.1.1 rfl) hr

omit package_sem in
/-- A byte's typed points-to is its heap points-to. -/
theorem w8_typedPointsto_heap (l : Loc) (b : w8) (dq : DFrac) :
    typedPointsto (GF := GF) l b dq ⊢ heapPointsto l dq #b := by
  rw [typedPointsto_unseal_eq]
  change iprop(heapPointsto l dq #b ∗ ⌜l ≠ null⌝) ⊢ _
  iintro ⟨H, -⟩
  iexact H

omit package_sem in
theorem sliceIndexRef_slice0 (s : GoSlice) (high : w64) :
    sliceIndexRef w8 0 (slice.slice s w8 (W64 0) high) = sliceIndexRef w8 0 s := by
  simp [slice.slice, sliceIndexRef, go.arrayIndexRef_0]

set_option maxHeartbeats 2000000 in
/-- The model's `retireLoop s`: a write begun and never finished on each byte of `s`, which takes
the bytes for good. -/
theorem wp_retireLoop :
    ⊢ ∀ (s : GoSlice) (vs : List w8) (Φ : val → IProp GF),
      (s ↦* vs : IProp GF) -∗ Φ #() -∗ WP (App (Val retireLoop) (Val #s)) {{ Φ }} := by
  unfold retireLoop
  iloeb as IH
  iintro %s %vs %Φ Hs HΦ
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hwf := ownSlice_wf s _ vs $$ Hs
  wp_pures
  wp_if_destruct
  · obtain ⟨v, hv⟩ : ∃ v, vs[0]? = some v := ⟨_, List.getElem?_eq_getElem (by word)⟩
    icases (ownSlice_split_all (W64 1) s _ vs ⟨by decide, by word⟩).1 $$ Hs with ⟨H0, Hrest⟩
    have hv0 : (vs.take (sint.nat (W64 1)))[(0 : Int).toNat]? = some v := by
      rw [show sint.nat (W64 1) = 1 from rfl]; simpa using hv
    icases ownSlice_elem_acc 0 v _ _ _ (Int.le_refl 0) hv0 $$ H0 with ⟨Hv, -⟩
    rw [sliceIndexRef_slice0] at *
    ihave Hv := w8_typedPointsto_heap _ _ _ $$ Hv
    wp_pures
    rw [if_pos ⟨Int.le_refl _, by word⟩]
    rw [show sint.Z (W64 0) = 0 from rfl]
    wp_bind (PrepareWrite _)
    wp_apply_core (wp_prepare_write (sliceIndexRef w8 0 s) #v) $$ Hv
    iintro -
    wp_pures
    rw [if_pos ⟨by decide, by word, Hwf.2⟩]
    iapply IH $$ Hrest HΦ
  · iexact HΦ

set_option maxHeartbeats 2000000 in
/-- The model's `fillArbitraryBytes s`: an arbitrary byte in each element of `s`. -/
theorem wp_fillArbitraryBytes :
    ⊢ ∀ (s : GoSlice) (vs : List w8) (Φ : val → IProp GF),
      (s ↦* vs : IProp GF) -∗
      (∀ vs' : List w8, s ↦* vs' -∗ ⌜vs'.length = vs.length⌝ -∗ Φ #()) -∗
      WP (App (Val fillArbitraryBytes) (Val #s)) {{ Φ }} := by
  unfold fillArbitraryBytes
  iloeb as IH
  iintro %s %vs %Φ Hs HΦ
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hwf := ownSlice_wf s _ vs $$ Hs
  wp_pures
  wp_if_destruct
  · wp_pures
    rw [if_pos ⟨Int.le_refl _, by word⟩]
    wp_apply wp_ArbitraryInt as %x -
    wp_pures
    rw [show sint.Z (W64 0) = 0 from rfl]
    wp_apply (wp_store_slice_index s 0 vs (W8 (uint.Z x)) (V := w8) (t := go.byte)) $$ [$Hs]
      as Hs
    · ipureintro; constructor <;> word
    icases (ownSlice_split_all (W64 1) s _ _ ⟨by decide, by word⟩).1 $$ Hs with ⟨H0, Hrest⟩
    wp_pures
    rw [if_pos ⟨by decide, by word, Hwf.2⟩]
    iapply IH $$ Hrest
    iintro %vs' Hrest %Hl
    have hAlen : ((vs.set (Int.toNat 0) (W8 (uint.Z x))).take (sint.nat (W64 1))).length =
        sint.nat (W64 1) := by
      rw [List.length_take, List.length_set, show sint.nat (W64 1) = 1 from rfl]; word
    iapply HΦ $$ %(((vs.set (Int.toNat 0) (W8 (uint.Z x))).take (sint.nat (W64 1))) ++ vs') [H0 Hrest]
    · iapply (ownSlice_split_all (W64 1) s _
        (((vs.set (Int.toNat 0) (W8 (uint.Z x))).take (sint.nat (W64 1))) ++ vs')
        ⟨by decide, by word⟩).2
      rw [List.take_left' hAlen, List.drop_left' hAlen]
      iframe
    · ipureintro
      rw [List.length_append, hAlen, Hl, List.length_drop, List.length_set]
      word
  · iapply HΦ $$ Hs
    ipureintro; rfl

set_option maxHeartbeats 2000000 in
/-- The model's `printerAlloc n`: a slice of `n` zeros with its capacity (`nil` for some `n = 0`). -/
theorem wp_printerAlloc (n : w64) (hn : 0 ≤ sint.Z n) :
    {{ (True : IProp GF) }}
      (App (Val printerAlloc) (Val #n))
    {{ (b : GoSlice), RET #b; b ↦* List.replicate (sint.nat n) (zero_val w8) ∗
        ownSliceCap w8 b (DFrac.own 1) }} := by
  iintro %Φ - HΦ
  unfold printerAlloc
  wp_pures
  wp_if_destruct
  · wp_apply wp_ArbitraryInt as %x -
    wp_pures
    wp_if_destruct
    · iapply HΦ
      rw [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero]
      isplitl []
      · iapply ownSlice_nil
      · iapply ownSliceCap_nil
    · wp_apply wp_new_cap as %c %Hc
      wp_apply (wp_slice_make3 (V := w8) _ c ⟨by word, Hc⟩) as %b ⟨Hb, Hcap, -⟩
      iapply HΦ; iframe
  · wp_apply wp_new_cap as %c %Hc
    wp_apply (wp_slice_make3 (V := w8) n c ⟨hn, Hc⟩) as %b ⟨Hb, Hcap, -⟩
    iapply HΦ; iframe

set_option maxHeartbeats 2000000 in
/-- The model's `printerBuf s`: a new slice holding `s`, with its spare capacity (some bytes). -/
theorem wp_printerBuf (s : GoString) :
    {{ (True : IProp GF) }}
      (App (Val printerBuf) (Val #s))
    {{ (b : GoSlice), RET #b; b ↦* s ∗ ∃ vs : List w8, slice.slice b w8 b.len b.cap ↦* vs }} := by
  iintro %Φ - HΦ
  unfold printerBuf
  wp_pures
  wp_apply wp_string_to_bytes s as %src ⟨Hsrc, -⟩
  ihave %Hsl := ownSlice_len $$ Hsrc
  wp_pures
  wp_apply (wp_printerAlloc src.len Hsl.2) as %b ⟨Hb, Hcap⟩
  ihave %Hblen := ownSlice_len $$ Hb
  ihave %Hbwf := ownSlice_wf b _ _ $$ Hb
  icases ownSliceCap_split (V := w8) b.cap b $$ [$Hcap] with ⟨%vs0, Hspare, -⟩
  · ipureintro; constructor <;> word
  have hbl : src.len = b.len := by
    have := Hblen.1; rw [List.length_replicate] at this; word
  wp_pures
  rw [hbl, if_pos ⟨Hbwf.1, Hbwf.2, by word⟩]
  wp_bind (App (Val fillArbitraryBytes) _)
  iapply wp_fillArbitraryBytes $$ Hspare
  iintro %vs' Hspare %-
  wp_pures
  wp_apply (wp_slice_copy (V := w8) b _ src s (DFrac.own 1)) $$ [$Hb $Hsrc] as %m ⟨%Hm, Hb, -⟩
  wp_pures
  iapply HΦ
  have hsb : s.length = sint.nat b.len := by rw [Hsl.1, hbl]
  have hlist : List.take (List.replicate (sint.nat b.len) (zero_val w8)).length s ++
      List.drop s.length (List.replicate (sint.nat b.len) (zero_val w8)) = s := by
    rw [List.length_replicate, ← hsb, List.take_length, List.drop_eq_nil_of_le (by simp),
      List.append_nil]
  rw [hlist]
  iframe

/-- The model's `retire b`: a write begun and never finished on each byte of `b` up to its capacity,
which takes the bytes and the spare capacity for good. -/
theorem wp_retire (b : GoSlice) (bs vs : List w8) :
    {{ (b ↦* bs ∗ slice.slice b w8 b.len b.cap ↦* vs : IProp GF) }}
      (App (Val retire) (Val #b))
    {{ RET #(); True }} := by
  iintro %Φ ⟨Hb, Hs⟩ HΦ
  ihave %Hwf := ownSlice_wf b _ bs $$ Hb
  unfold retire
  wp_pures
  wp_bind (App (Val retireLoop) (Val #b))
  iapply wp_retireLoop $$ Hb
  wp_pures
  rw [if_pos ⟨Hwf.1, Hwf.2, by word⟩]
  iapply wp_retireLoop $$ Hs
  iapply HΦ
  itrivial

end wps

end fmt

end Perennial
