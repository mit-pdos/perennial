/-
Shared definitions of the proofs of the Go model of string/byte-slice conversions
(`github.com/mit-pdos/perennial/goose/model/strings`, used by
`Perennial/Golang/Theory/String.lean`): the spec of the builtin `len` on strings, which
its functions call.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory.Pre
public import Perennial.Golang.Defn.String
public import Perennial.Code.github_com.mit_pdos.perennial.goose.model.strings
public import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.model.strings

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.mit_pdos.perennial.goose.model.strings

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : go.StringSemantics]
variable {s : Stuckness} {E : CoPset}

theorem wp_string_len (str : GoString) {t : go.GoType} [t ↓u go.string] :
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

end wps

end github_com.mit_pdos.perennial.goose.model.strings

namespace go

/-! The runes of a string, as a range loop over it decodes them (Go's UTF-8 decoding,
`runtime.decoderune`, with the words it computes). -/

/-- The rune `U+FFFD` of an invalid UTF-8 sequence. -/
def runeError : w32 := W32 0xFFFD

/-- What `decoderune` decodes from `t`, the string from the byte to decode on: the rune
and its length in bytes (`(runeError, 1)` for an invalid sequence). -/
def decodeMulti (t : GoString) : w32 × Nat :=
  let b (i : Nat) : w8 := t.getD i 0
  let cont (i : Nat) : Prop := i < t.length ∧ 0x80 ≤ uint.Z (b i) ∧ uint.Z (b i) ≤ 0xBF
  let c (i : Nat) (m : w8) : w32 := W32 (uint.Z (b i &&& m))
  if 0xC0 ≤ uint.Z (b 0) ∧ uint.Z (b 0) < 0xE0 then
    let r := (c 0 (W8 0x1F) <<< (W64 6)) ||| c 1 (W8 0x3F)
    if cont 1 ∧ 0x7F < sint.Z r then (r, 2) else (runeError, 1)
  else if 0xE0 ≤ uint.Z (b 0) ∧ uint.Z (b 0) < 0xF0 then
    let r := ((c 0 (W8 0x0F) <<< (W64 12)) ||| (c 1 (W8 0x3F) <<< (W64 6))) ||| c 2 (W8 0x3F)
    if cont 1 ∧ cont 2 ∧ 0x7FF < sint.Z r ∧ ¬ (0xD800 ≤ sint.Z r ∧ sint.Z r ≤ 0xDFFF) then (r, 3)
    else (runeError, 1)
  else if 0xF0 ≤ uint.Z (b 0) ∧ uint.Z (b 0) < 0xF8 then
    let r := (((c 0 (W8 0x07) <<< (W64 18)) ||| (c 1 (W8 0x3F) <<< (W64 12))) |||
      (c 2 (W8 0x3F) <<< (W64 6))) ||| c 3 (W8 0x3F)
    if cont 1 ∧ cont 2 ∧ cont 3 ∧ 0xFFFF < sint.Z r ∧ sint.Z r ≤ 0x10FFFF then (r, 4)
    else (runeError, 1)
  else (runeError, 1)

/-- The rune at byte index `k` of `s` and the index after it (`DecodeRune`): a byte below
`0x80` is a rune by itself. -/
def decodeRune (s : GoString) (k : Nat) : w32 × Nat :=
  let b := (s.drop k).getD 0 0
  if uint.Z b < 0x80 then (W32 (uint.Z b), k + 1)
  else ((decodeMulti (s.drop k)).1, k + (decodeMulti (s.drop k)).2)

theorem decodeMulti_len (t : GoString) :
    1 ≤ (decodeMulti t).2 ∧ ((decodeMulti t).2 = 1 ∨ (decodeMulti t).2 ≤ t.length) := by
  unfold decodeMulti
  simp only
  repeat' split
  all_goals omega

theorem decodeRune_snd (s : GoString) (k : Nat) (hk : k < s.length) :
    k < (decodeRune s k).2 ∧ (decodeRune s k).2 ≤ s.length := by
  have := decodeMulti_len (s.drop k)
  unfold decodeRune
  simp only [List.length_drop] at this ⊢
  split <;> simp only <;> omega

/-- The iterations of a range loop over `s` from byte index `k` on, with `fuel` bounding
their number: each rune's start index and value. -/
def runesFrom (s : GoString) : (fuel k : Nat) → List (Nat × w32)
  | 0, _ => []
  | fuel + 1, k =>
    if k < s.length then (k, (decodeRune s k).1) :: runesFrom s fuel (decodeRune s k).2 else []

/-- The iterations of a range loop over `s`: each rune's start index and value. -/
def runes (s : GoString) : List (Nat × w32) := runesFrom s s.length 0

/-- Enough fuel to reach the end of `s` gives the same iterations. -/
theorem runesFrom_fuel (s : GoString) (fuel fuel' k : Nat)
    (h : s.length - k ≤ fuel) (h' : s.length - k ≤ fuel') :
    runesFrom s fuel k = runesFrom s fuel' k := by
  induction fuel generalizing fuel' k with
  | zero =>
    cases fuel' with
    | zero => rfl
    | succ f' => simp [runesFrom]; omega
  | succ f ih =>
    cases fuel' with
    | zero => simp [runesFrom]; omega
    | succ f' =>
      simp only [runesFrom]
      by_cases hk : k < s.length
      · have := decodeRune_snd s k hk
        simp only [hk, ↓reduceIte]
        rw [ih f' _ (by omega) (by omega)]
      · simp only [hk, ↓reduceIte]

theorem runesFrom_cons (s : GoString) (k : Nat) (hk : k < s.length) :
    runesFrom s (s.length - k) k =
      (k, (decodeRune s k).1) :: runesFrom s (s.length - (decodeRune s k).2) (decodeRune s k).2 := by
  have := decodeRune_snd s k hk
  obtain ⟨f, hf⟩ : ∃ f, s.length - k = f + 1 := ⟨s.length - k - 1, by omega⟩
  rw [hf]
  simp only [runesFrom, hk, ↓reduceIte]
  rw [runesFrom_fuel s f (s.length - (decodeRune s k).2) (decodeRune s k).2 (by omega) (by omega)]

theorem runesFrom_end (s : GoString) (k : Nat) (hk : s.length ≤ k) :
    runesFrom s (s.length - k) k = [] := by
  rw [show s.length - k = 0 by omega]; rfl

end go

end Perennial
