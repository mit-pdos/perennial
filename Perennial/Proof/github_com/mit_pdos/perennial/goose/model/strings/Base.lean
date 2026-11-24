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
  by_cases h : (str.length : Int) ≤ maxAddr
  · rw [ite_eq_left h]
    wp_pures
    iapply HΦ
    ipureintro; unfold maxAddr at h; omega
  · rw [ite_eq_right h]
    iapply wp_AngelicExit

/-- `len(s)` of a string: no longer than the address space (`maxAddr`), as a slice. -/
theorem wp_string_len_maxAddr (str : GoString) {t : go.GoType} [t ↓u go.string] :
    {{ (True : IProp GF) }}
      (App (Val #(functions go.len [t])) (Val #str)) @ s; E
    {{ RET #(W64 str.length); ⌜(str.length : Int) ≤ maxAddr⌝ }} := by
  wp_start
  by_cases h : (str.length : Int) ≤ maxAddr
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

/-! ## What the decoding of a range loop says about the bytes -/

/-- `runeError` is not ASCII. -/
theorem runeError_sint : sint.Z runeError = 0xFFFD := by
  unfold runeError; word

/-- A multi-byte decoding gives `runeError` or a rune above `0x7F`. -/
theorem decodeMulti_fst (t : GoString) :
    (decodeMulti t).1 = runeError ∨ 0x7F < sint.Z (decodeMulti t).1 := by
  unfold decodeMulti
  simp only
  repeat' split
  all_goals first
    | exact Or.inl rfl
    | (right; rename_i h; simp only at h ⊢; omega)

/-- The bytes after the first of a multi-byte decoding are continuation bytes of `t`. -/
theorem decodeMulti_cont (t : GoString) :
    ∀ i, 0 < i → i < (decodeMulti t).2 → i < t.length ∧ 0x80 ≤ uint.Z (t.getD i 0) := by
  unfold decodeMulti
  simp only
  split
  · split
    · rename_i h
      intro i h0 hi
      simp only at hi
      have : i = 1 := by omega
      subst this
      exact ⟨h.1.1, h.1.2.1⟩
    · intro i h0 hi; simp only at hi; omega
  · split
    · split
      · rename_i h
        intro i h0 hi
        simp only at hi
        rcases (by omega : i = 1 ∨ i = 2) with rfl | rfl
        · exact ⟨h.1.1, h.1.2.1⟩
        · exact ⟨h.2.1.1, h.2.1.2.1⟩
      · intro i h0 hi; simp only at hi; omega
    · split
      · split
        · rename_i h
          intro i h0 hi
          simp only at hi
          rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
          · exact ⟨h.1.1, h.1.2.1⟩
          · exact ⟨h.2.1.1, h.2.1.2.1⟩
          · exact ⟨h.2.2.1.1, h.2.2.1.2.1⟩
        · intro i h0 hi; simp only at hi; omega
      · intro i h0 hi; simp only at hi; omega

/-- An ASCII byte is a rune by itself. -/
theorem decodeRune_ascii (s : GoString) (k : Nat) (b : w8) (hb : s[k]? = some b)
    (hlt : uint.Z b < 0x80) : decodeRune s k = (W32 (uint.Z b), k + 1) := by
  have hd : (s.drop k).getD 0 0 = b := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero, hb]; rfl
  unfold decodeRune
  simp only [hd, hlt, ↓reduceIte]

/-- A rune decoded from a non-ASCII byte is above `0x7F`. -/
theorem decodeRune_nonascii (s : GoString) (k : Nat) (b : w8) (hb : s[k]? = some b)
    (hge : 0x80 ≤ uint.Z b) : 0x7F < sint.Z (decodeRune s k).1 := by
  have hd : (s.drop k).getD 0 0 = b := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero, hb]; rfl
  unfold decodeRune
  simp only [hd, show ¬ uint.Z b < 0x80 by omega, ↓reduceIte]
  rcases decodeMulti_fst (s.drop k) with h | h
  · rw [h, runeError_sint]; omega
  · exact h

/-- The bytes between a rune's first byte and the next rune are continuation bytes. -/
theorem decodeRune_cont (s : GoString) (k p : Nat) (hk : k < p) (hp : p < (decodeRune s k).2) :
    ∃ b, s[p]? = some b ∧ 0x80 ≤ uint.Z b := by
  unfold decodeRune at hp
  simp only at hp
  split at hp
  · simp only at hp; omega
  · simp only at hp
    have := decodeMulti_cont (s.drop k) (p - k) (by omega) (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop, show k + (p - k) = p by omega] at this
    rw [List.length_drop] at this
    obtain ⟨hl, hc⟩ := this
    refine ⟨s[p]'(by omega), List.getElem?_eq_getElem (by omega), ?_⟩
    rw [List.getElem?_eq_getElem (by omega)] at hc
    exact hc

/-- What `runesFrom` lists: runes at increasing indices from `k` on, each the decoding at its
index. -/
theorem runesFrom_mem (s : GoString) (fuel : Nat) :
    ∀ (k : Nat), ∀ e ∈ runesFrom s fuel k, k ≤ e.1 ∧ e.1 < s.length ∧
      e.2 = (decodeRune s e.1).1 := by
  induction fuel with
  | zero => intro k e he; simp [runesFrom] at he
  | succ fuel ih =>
    intro k e he
    simp only [runesFrom] at he
    split at he
    · rename_i hk
      rcases List.mem_cons.1 he with rfl | he
      · exact ⟨Nat.le_refl _, hk, by dsimp only⟩
      · have h1 := ih _ e he
        have h2 := decodeRune_snd s k hk
        exact ⟨by omega, h1.2.1, h1.2.2⟩
    · nomatch he

theorem runesFrom_pairwise (s : GoString) (fuel : Nat) :
    ∀ (k : Nat), (runesFrom s fuel k).Pairwise (fun a b => a.1 < b.1) := by
  induction fuel with
  | zero => intro k; simp [runesFrom]
  | succ fuel ih =>
    intro k
    simp only [runesFrom]
    split
    · rename_i hk
      refine List.pairwise_cons.2 ⟨fun e he => ?_, ih _⟩
      have h1 := (runesFrom_mem s fuel _ e he).1
      have h2 := decodeRune_snd s k hk
      simp only; omega
    · exact List.Pairwise.nil

/-- Every ASCII byte of `s` past `k` is a rune of `runesFrom s _ k`. -/
theorem runesFrom_ascii (s : GoString) (fuel : Nat) :
    ∀ (k p : Nat) (b : w8), s.length - k ≤ fuel → k ≤ p → s[p]? = some b →
      uint.Z b < 0x80 → (p, W32 (uint.Z b)) ∈ runesFrom s fuel k := by
  induction fuel with
  | zero =>
    intro k p b hf hkp hb _
    have := (List.getElem?_eq_some_iff.1 hb).1; omega
  | succ fuel ih =>
    intro k p b hf hkp hb hlt
    have hp := (List.getElem?_eq_some_iff.1 hb).1
    have hk : k < s.length := by omega
    simp only [runesFrom, hk, ↓reduceIte]
    rcases Nat.lt_or_ge k p with hkp' | hkp'
    · refine List.mem_cons_of_mem _ (ih _ p b ?_ ?_ hb hlt)
      · have := decodeRune_snd s k hk; omega
      · refine Classical.byContradiction fun hc => ?_
        obtain ⟨b', hb', hge⟩ := decodeRune_cont s k p hkp' (by omega)
        rw [hb] at hb'; cases hb'; omega
    · have : p = k := by omega
      subst this
      rw [decodeRune_ascii s p b hb hlt]
      exact List.mem_cons_self

theorem runes_mem (s : GoString) (e : Nat × w32) (he : e ∈ runes s) :
    e.1 < s.length ∧ e.2 = (decodeRune s e.1).1 :=
  let h := runesFrom_mem s _ _ e he; ⟨h.2.1, h.2.2⟩

theorem runes_pairwise (s : GoString) : (runes s).Pairwise (fun a b => a.1 < b.1) :=
  runesFrom_pairwise s _ _

/-- Every ASCII byte of `s` is a rune of a range loop over `s`. -/
theorem runes_ascii (s : GoString) (p : Nat) (b : w8) (hb : s[p]? = some b)
    (hlt : uint.Z b < 0x80) : (p, W32 (uint.Z b)) ∈ runes s :=
  runesFrom_ascii s _ 0 p b (by omega) (Nat.zero_le _) hb hlt

/-- A rune below `0x80` of a range loop over `s` is the byte at its index. -/
theorem runes_lt_0x80 (s : GoString) (e : Nat × w32) (he : e ∈ runes s)
    (hlt : 0 ≤ sint.Z e.2 ∧ sint.Z e.2 < 0x80) :
    ∃ b, s[e.1]? = some b ∧ uint.Z b < 0x80 ∧ e.2 = W32 (uint.Z b) := by
  obtain ⟨hl, he2⟩ := runes_mem s e he
  obtain ⟨b, hb⟩ : ∃ b, s[e.1]? = some b := ⟨_, List.getElem?_eq_getElem hl⟩
  rcases Nat.lt_or_ge (uint.Z b).toNat 0x80 with h | h
  · have h' : uint.Z b < 0x80 := by omega
    rw [decodeRune_ascii s e.1 b hb h'] at he2
    exact ⟨b, hb, h', he2⟩
  · have := decodeRune_nonascii s e.1 b hb (by omega)
    rw [← he2] at this; omega

end go

end Perennial
