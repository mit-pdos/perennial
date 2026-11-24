/-
Pure lemmas of the proof of `fmt.(*pp).doPrintf`: `parsenumSpec` on the digits of a `%0N`
directive, the leading literal pieces of a format (`leadLits`), what `encode`, `Fits` and `Out`
say about them.
-/
module

public import Perennial.Proof.fmt.PrintDefs

@[expose] public section

noncomputable section

namespace Perennial

namespace fmt

/-! ## `parsenum` -/

/-- A decimal digit `0`–`9`. -/
def IsDigit (c : w8) : Prop := 48 ≤ uint.nat c ∧ uint.nat c ≤ 57

/-- One step of `parsenum`'s accumulation: `num*10 + int(c-'0')`. -/
def digitStep (num : Nat) (c : w8) : Nat := num * 10 + (uint.nat c - 48)

theorem le_foldl_digitStep (ds : GoString) (a : Nat) : a ≤ ds.foldl digitStep a := by
  induction ds generalizing a with
  | nil => simp
  | cons c ds ih =>
    simp only [List.foldl_cons]
    have := ih (digitStep a c)
    unfold digitStep at this ⊢
    omega

/-- `parsenumLoop` reads the digits `ds` (whose value stays at most `10^6`) up to the first
non-digit. -/
theorem parsenumLoop_digits (s ds rest : GoString) (i num : Nat) (isnum : Bool)
    (hs : s.drop i = ds ++ rest) (hds : ∀ c ∈ ds, IsDigit c)
    (hrest : ∀ c, rest.head? = some c → ¬ IsDigit c)
    (hb : ds.foldl digitStep num ≤ 1000000) :
    parsenumLoop s s.length i num isnum =
      (ds.foldl digitStep num, isnum || !ds.isEmpty, i + ds.length) := by
  induction ds generalizing i num isnum with
  | nil =>
    simp only [List.nil_append] at hs
    simp only [List.foldl_nil, List.isEmpty_nil, Bool.not_true, Bool.or_false, List.length_nil,
      Nat.add_zero]
    rw [parsenumLoop]
    split
    · have hl : s[i]? = rest.head? := by rw [← hs, List.head?_drop]
      split
      · rename_i c hc
        rw [hc] at hl
        have := hrest c hl.symm
        unfold IsDigit at this
        rw [if_neg this]
      · rfl
    · rfl
  | cons c ds ih =>
    have hl : s[i]? = some c := by rw [← List.head?_drop, hs]; rfl
    have hlt : i < s.length := by
      have := (List.getElem?_eq_some_iff.mp hl).1; omega
    have hc : IsDigit c := hds c (by simp)
    have hle : num ≤ 1000000 := by
      have h1 := le_foldl_digitStep ds (digitStep num c)
      have h2 : num ≤ digitStep num c := by unfold digitStep; omega
      simp only [List.foldl_cons] at hb
      omega
    unfold IsDigit at hc
    rw [parsenumLoop, if_pos hlt, hl]
    simp only
    rw [if_pos hc, if_neg (by omega)]
    have hs' : s.drop (i + 1) = ds ++ rest := by
      rw [← List.drop_drop, hs]; rfl
    rw [show num * 10 + (uint.nat c - 48) = digitStep num c from rfl,
      ih (i + 1) (digitStep num c) true hs' (fun c' h => hds c' (by simp [h]))
      (by simpa using hb)]
    simp only [List.foldl_cons, digitStep, Bool.true_or, List.isEmpty_cons, Bool.not_false,
      Bool.or_true, List.length_cons]
    simp only [Prod.mk.injEq, true_and]
    omega

theorem foldl_digitStep_decimalNat (n : Nat) : (decimalNat n).foldl digitStep 0 = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    have hd : uint.nat (digitByte (n % 10)) = 48 + n % 10 := by
      have : n % 10 < 10 := Nat.mod_lt _ (by omega)
      unfold digitByte; word
    by_cases h : n < 10
    · rw [decimalNat_of_lt h]
      simp only [List.foldl_cons, List.foldl_nil, digitStep]
      rw [Nat.mod_eq_of_lt h] at hd
      rw [hd]; omega
    · rw [decimalNat_of_ge (by omega), List.foldl_append, ih (n / 10) (by omega)]
      simp only [List.foldl_cons, List.foldl_nil, digitStep]
      rw [hd]; omega

theorem decimalNat_isDigit (n : Nat) : ∀ c ∈ decimalNat n, IsDigit c := by
  intro c hc
  have := decimalNat_digits n c hc
  unfold IsDigit; word

/-- `parsenum` on the digits of `N ≤ 10^6` followed by a non-digit (or the end). -/
theorem parsenumSpec_decimalNat (s rest : GoString) (i N : Nat)
    (hs : s.drop i = decimalNat N ++ rest) (hrest : ∀ c, rest.head? = some c → ¬ IsDigit c)
    (hN : N ≤ 1000000) :
    parsenumSpec s i s.length = (N, true, i + (decimalNat N).length) := by
  have hlen : i + (decimalNat N).length ≤ s.length := by
    have := congrArg List.length hs
    simp only [List.length_drop, List.length_append] at this
    have := length_decimalNat_pos N
    omega
  have hpos := length_decimalNat_pos N
  unfold parsenumSpec
  rw [if_neg (by omega), parsenumLoop_digits s (decimalNat N) rest i 0 false hs
    (decimalNat_isDigit N) hrest (by rw [foldl_digitStep_decimalNat]; exact hN),
    foldl_digitStep_decimalNat]
  have : (decimalNat N).isEmpty = false := by
    cases h : decimalNat N
    · exact absurd h (decimalNat_ne_nil N)
    · rfl
  simp [this]

/-- `parsenum` at a non-digit. -/
theorem parsenumSpec_nondigit (s : GoString) (i : Nat) (c : w8) (hs : s[i]? = some c)
    (hc : ¬ IsDigit c) : parsenumSpec s i s.length = (0, false, i) := by
  have hlt : i < s.length := (List.getElem?_eq_some_iff.mp hs).1
  unfold parsenumSpec
  rw [if_neg (by omega), parsenumLoop_digits s [] (s.drop i) i 0 false (by simp) (by simp)
    (fun c' h => by rw [List.head?_drop, hs] at h; cases h; exact hc) (by simp)]
  simp

/-! ## The pieces -/

/-- The leading literal pieces of `ps`: their bytes, and the pieces after them. -/
def leadLits : List Piece → GoString × List Piece
  | .lit s :: ps => ((s ++ (leadLits ps).1), (leadLits ps).2)
  | ps => ([], ps)

theorem leadLits_lit (s : GoString) (ps : List Piece) :
    leadLits (.lit s :: ps) = (s ++ (leadLits ps).1, (leadLits ps).2) := rfl

theorem encode_nil : encode [] = [] := rfl

theorem encode_cons (p : Piece) (ps : List Piece) : encode (p :: ps) = p.encode ++ encode ps := by
  simp [encode]

theorem encode_leadLits (ps : List Piece) :
    encode ps = (leadLits ps).1 ++ encode (leadLits ps).2 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    cases p with
    | lit s => rw [leadLits_lit, encode_cons, ih]; simp [Piece.encode]
    | percent => rfl
    | dir zw v => rfl

/-- What comes after the leading literals: nothing, `%%`, or a directive. -/
theorem leadLits_rest (ps : List Piece) :
    (leadLits ps).2 = [] ∨ (∃ ps', (leadLits ps).2 = .percent :: ps') ∨
      (∃ zw v ps', (leadLits ps).2 = .dir zw v :: ps') := by
  induction ps with
  | nil => exact Or.inl rfl
  | cons p ps ih =>
    cases p with
    | lit s => rw [leadLits_lit]; exact ih
    | percent => exact Or.inr (Or.inl ⟨ps, rfl⟩)
    | dir zw v => exact Or.inr (Or.inr ⟨zw, v, ps, rfl⟩)

theorem Fits_leadLits {ps : List Piece} {args : List Arg} (h : Fits ps args) :
    W8 37 ∉ (leadLits ps).1 ∧ Fits (leadLits ps).2 args := by
  induction h with
  | nil => exact ⟨by simp [leadLits], Fits.nil⟩
  | lit s ps args hs _ ih =>
    rw [leadLits_lit]
    refine ⟨?_, ih.2⟩
    simp only [List.mem_append, not_or]
    exact ⟨hs, ih.1⟩
  | percent ps args hf => exact ⟨by simp [leadLits], Fits.percent ps args hf⟩
  | dir zw v a ps args hd hf => exact ⟨by simp [leadLits], Fits.dir zw v a ps args hd hf⟩

theorem Out_leadLits {ps : List Piece} {args : List Arg} {o : GoString}
    (h : Out (leadLits ps).2 args o) : Out ps args ((leadLits ps).1 ++ o) := by
  induction ps generalizing o with
  | nil => exact h
  | cons p ps ih =>
    cases p with
    | lit s =>
      rw [leadLits_lit] at h ⊢
      rw [List.append_assoc]
      exact Out.lit s ps args _ (ih h)
    | percent => exact h
    | dir zw v => exact h

/-- A format with no bytes left: only empty literals, no argument, no output. -/
theorem Fits_encode_nil {ps : List Piece} {args : List Arg} (h : Fits ps args)
    (he : encode ps = []) : args = [] ∧ Out ps args [] := by
  induction h with
  | nil => exact ⟨rfl, Out.nil⟩
  | lit s ps args _ _ ih =>
    rw [encode_cons] at he
    simp only [Piece.encode, List.append_eq_nil_iff] at he
    obtain ⟨rfl, he⟩ := he
    obtain ⟨h1, h2⟩ := ih he
    exact ⟨h1, by simpa using Out.lit [] ps args [] h2⟩
  | percent ps args _ _ => simp [encode_cons, Piece.encode] at he
  | dir zw v a ps args _ _ _ =>
    cases zw <;> simp [encode_cons, Piece.encode] at he

/-- The `k`-th byte of `L` where `format.drop i = L ++ R`. -/
theorem getElem?_of_drop_append {format L R : GoString} {i k : Nat}
    (h : format.drop i = L ++ R) : format[i + k]? = (L ++ R)[k]? := by
  rw [← h, List.getElem?_drop]

end fmt

end Perennial
