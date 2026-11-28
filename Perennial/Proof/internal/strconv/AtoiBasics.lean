/-
The pure facts `Atoi`'s proof needs (`internal/strconv/atoi.go`): its fast path (1 to 18 bytes, an
optional sign, then a loop of digits `ch - '0' ≤ 9`) computes what `parseInt s 10 0` says, and
`parseInt` at bit size 0 is `parseInt` at 64, so `Atoi` reads back what `FormatInt(m, 10)` writes.
-/
module

public import Perennial.Proof.internal.strconv.FormatBasics

@[expose] public section

noncomputable section

namespace Perennial

namespace internal.strconv

/-- Bit size 0 is bit size 64 (`IntSize`). -/
theorem parseInt_bitSize0 (s : GoString) (base : Nat) : parseInt s base 0 = parseInt s base 64 := rfl

/-- `ParseInt(s, 10, 0)` reads back what `FormatInt(m, 10)` writes. -/
theorem parseInt_fmtInt10_0 (m : w64) : parseInt (fmtInt m (W64 10)) 10 0 = .ok (sint.Z m) :=
  parseInt_fmtInt10 m

/-- The byte `x` is a decimal digit when `x - '0'`, in `uint8`, is at most 9 (`Atoi`'s test): its
value as `ParseUint` reads it. -/
theorem digitVal_of_sub_le (x : w8) (h : uint.nat (x - W8 48) ≤ 9) :
    digitVal x = some (uint.nat (x - W8 48)) := by
  have h1 : 48 ≤ uint.nat x ∧ uint.nat x ≤ 57 := by revert h; word
  have h2 : uint.nat (x - W8 48) = uint.nat x - 48 := by revert h1; word
  unfold digitVal
  rw [ite_eq_left h1, h2]

/-- A byte with `x - '0' > 9` in `uint8` is not a decimal digit: `ParseUint` reads it as no digit,
or as a digit of value at least 10. -/
theorem digitVal_of_sub_gt (x : w8) (h : 9 < uint.nat (x - W8 48)) :
    digitVal x = none ∨ ∃ d, digitVal x = some d ∧ 10 ≤ d := by
  have h1 : ¬ (48 ≤ uint.nat x ∧ uint.nat x ≤ 57) := by revert h; word
  unfold digitVal
  rw [ite_eq_right h1]
  split
  · exact Or.inr ⟨_, rfl, by omega⟩
  · exact Or.inl rfl

/-- `ParseUint`'s decimal loop stops with a syntax error at a byte with `x - '0' > 9`. -/
theorem parseDigits10_cons_gt {maxVal : Nat} {x : w8} {cs : GoString} {n : Nat}
    (h : 9 < uint.nat (x - W8 48)) : parseDigits 10 maxVal (x :: cs) n = .errSyntax := by
  rcases digitVal_of_sub_gt x h with hd | ⟨d, hd, hd10⟩
  · exact parseDigits_cons_none hd
  · exact parseDigits_cons_ge hd hd10

/-- `ParseUint`'s decimal loop steps over a byte with `x - '0' ≤ 9`, when the value fits. -/
theorem parseDigits10_cons_le {maxVal : Nat} {x : w8} {cs : GoString} {n : Nat}
    (h : uint.nat (x - W8 48) ≤ 9) (hm : n * 10 + uint.nat (x - W8 48) ≤ maxVal) :
    parseDigits 10 maxVal (x :: cs) n = parseDigits 10 maxVal cs (n * 10 + uint.nat (x - W8 48)) :=
  parseDigits_cons_ok (digitVal_of_sub_le x h) (by omega) hm

/-- `ParseInt`'s result after the sign, from `ParseUint`'s syntax error. -/
theorem parseIntOf_of_errSyntax {neg : Bool} {t : GoString} {base bitSize : Nat}
    (h : parseUint t base bitSize = .errSyntax) : parseIntOf neg t base bitSize = .errSyntax := by
  unfold parseIntOf
  rw [h]

/-- `ParseInt`'s result after the sign, from a value `ParseUint` read that fits the signed range. -/
theorem parseIntOf_of_ok {neg : Bool} {t : GoString} {base bitSize v : Nat}
    (h : parseUint t base bitSize = .ok v) (hv : v < 2 ^ (effBitSize bitSize - 1)) :
    parseIntOf neg t base bitSize = .ok (if neg then -(v : Int) else v) := by
  unfold parseIntOf
  rw [h]
  simp only
  rw [ite_eq_right (by intro h'; cases neg <;> (simp at h'; omega)),
    ite_eq_right (by intro h'; cases neg <;> (simp at h'; omega))]

/-- `parseIntOf_of_ok` in base 10 at bit size 0 (`int64`). -/
theorem parseIntOf_of_ok10 {neg : Bool} {t : GoString} {v : Nat}
    (h : parseUint t 10 0 = .ok v) (hv : v < 2 ^ 63) :
    parseIntOf neg t 10 0 = .ok (if neg then -(v : Int) else v) :=
  parseIntOf_of_ok h (by simpa [effBitSize] using hv)

/-- `-n` of a word holding a natural number `v`. -/
theorem W64_neg_natCast (v : Nat) : -(W64 (v : Int)) = W64 (-(v : Int)) := by
  word

/-- The invariant of `Atoi`'s fast loop over the bytes `t` of the string after its sign, at index
`k`: the value `v` read so far is below `10 ^ k` (so it fits, for `k ≤ 18`), and `ParseUint`'s loop
over `t` is its loop over the rest from `v`. -/
def atoiLoopInv (t : GoString) (k v : Nat) : Prop :=
  v < 10 ^ k ∧ parseDigits 10 (2 ^ 64 - 1) t 0 = parseDigits 10 (2 ^ 64 - 1) (t.drop k) v

theorem atoiLoopInv_zero (t : GoString) : atoiLoopInv t 0 0 := by
  simp [atoiLoopInv]

/-- The loop's step over a digit `t[k]` (`x - '0' ≤ 9`). -/
theorem atoiLoopInv_step {t : GoString} {k v : Nat} {x : w8} (hlen : t.length ≤ 18)
    (hk : t[k]? = some x) (h : uint.nat (x - W8 48) ≤ 9) (hi : atoiLoopInv t k v) :
    atoiLoopInv t (k + 1) (v * 10 + uint.nat (x - W8 48)) := by
  obtain ⟨hv, heq⟩ := hi
  have hlt : k < t.length := by
    rcases Nat.lt_or_ge k t.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hk; cases hk
  have hk' : t[k] = x := by rw [List.getElem?_eq_getElem hlt] at hk; exact Option.some.inj hk
  have hpow : 10 ^ (k + 1) ≤ 10 ^ 18 := Nat.pow_le_pow_right (by decide) (by omega)
  have hnew : v * 10 + uint.nat (x - W8 48) < 10 ^ (k + 1) := by rw [Nat.pow_succ]; omega
  refine ⟨hnew, ?_⟩
  rw [heq, List.drop_eq_getElem_cons hlt, hk']
  exact parseDigits10_cons_le h (by have : (10 : Nat) ^ 18 < 2 ^ 64 - 1 := (by decide); omega)

/-- The loop's exit at a byte `t[k]` that is not a digit: `ParseUint` gives a syntax error. -/
theorem atoiLoopInv_bad {t : GoString} {k v : Nat} {x : w8} (hk : t[k]? = some x)
    (h : 9 < uint.nat (x - W8 48)) (hi : atoiLoopInv t k v) (ht : t ≠ []) :
    parseUint t 10 0 = .errSyntax := by
  obtain ⟨-, heq⟩ := hi
  have hlt : k < t.length := by
    rcases Nat.lt_or_ge k t.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hk; cases hk
  have hk' : t[k] = x := by rw [List.getElem?_eq_getElem hlt] at hk; exact Option.some.inj hk
  rw [parseUint_of_ne ht]
  show parseDigits 10 (2 ^ 64 - 1) t 0 = _
  rw [heq, List.drop_eq_getElem_cons hlt, hk']
  exact parseDigits10_cons_gt h

/-- The loop's end, past the last byte: `ParseUint` gives the value read, which fits `int64`. -/
theorem atoiLoopInv_done {t : GoString} {v : Nat} (hlen : t.length ≤ 18)
    (hi : atoiLoopInv t t.length v) (ht : t ≠ []) :
    parseUint t 10 0 = .ok v ∧ v < 2 ^ 63 := by
  obtain ⟨hv, heq⟩ := hi
  have hpow : 10 ^ t.length ≤ 10 ^ 18 := Nat.pow_le_pow_right (by decide) hlen
  refine ⟨?_, by have : (10 : Nat) ^ 18 < 2 ^ 63 := (by decide); omega⟩
  rw [parseUint_of_ne ht]
  show parseDigits 10 (2 ^ 64 - 1) t 0 = _
  rw [heq, List.drop_length]
  rfl

end internal.strconv

end Perennial
