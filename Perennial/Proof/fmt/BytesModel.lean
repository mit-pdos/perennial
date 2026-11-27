/-
Specs of the helpers of the model printer of `fmt` (`goose/model/overlay/fmt/printmodel.go`) that
format a `[]byte` argument: `hexNibble`, `quoteByte`, `quoteBytes` and `formatSlice`.
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
      (App (App (Val (@! hexNibble)) (Val #d)) (Val #upper))
    {{ (r : w8), RET #r; ⌜r = hexNibbleByte upper (uint.nat d)⌝ }} := by
  wp_start
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
      (App (Val (@! quoteByte)) (Val #c))
    {{ (s : GoString), RET #s; ⌜s = quotedByte c⌝ }} := by
  wp_start
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
      (App (Val (@! quoteBytes)) (Val #sl))
    {{ (s : GoString) (ok : Bool), RET (PairV #s #ok); sl ↦*{dq} bs ∗
        ⌜(ok = true ↔ ∀ b ∈ bs, uint.nat b < 128) ∧ (ok = true → s = quoteASCII bs)⌝ }} := by
  wp_start as Hsl
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
      (App (App (Val (@! hexBytes)) (Val #sl)) (Val #upper))
    {{ (s : GoString), RET #s; sl ↦*{dq} bs ∗ ⌜s = bytesHex upper bs⌝ }} := by
  wp_start as Hsl
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
      (App (Val (@! decBytes)) (Val #sl))
    {{ (s : GoString), RET #s; sl ↦*{dq} bs ∗ ⌜s = bytesDec bs⌝ }} := by
  wp_start as Hsl
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
      (App (Val (@! joinStrings)) (Val #sl))
    {{ (s : GoString), RET #s; sl ↦*{dq} ss ∗ ⌜s = stringsJoin ss⌝ }} := by
  wp_start as Hsl
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
      (App (App (App (Val (@! formatSlice)) (Val #format)) (Val #i)) (Val #x))
    {{ (s : GoString) (next : w64) (ok : Bool), RET (PairV (PairV #s #next) #ok);
        bytesArgOwn dqb B x ∗
        ⌜ok = true → sint.Z next = sint.Z i + 2 ∧ sint.Z i < sint.Z next ∧
          sint.Z next ≤ (format.length : Int) ∧
          (∀ args r, SprintfOutB B (format.drop (sint.nat next)) args r →
            SprintfOutB B (W8 37 :: format.drop (sint.nat i + 1)) (x :: args) (s ++ r)) ∧
          AuxStep format (sint.nat i) (sint.nat next)⌝ ∗
        ⌜ok = false → ∀ args, ¬ BytesSimple B (format.drop (sint.nat i + 1)) (x :: args) ∧
          ¬ StringsSimple B (format.drop (sint.nat i + 1)) (x :: args)⌝ }} := by
  wp_start as Hown
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

end wps

end fmt

end Perennial
