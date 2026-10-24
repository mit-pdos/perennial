/-
The pure model of `ParseUint` (`internal/strconv/atoi.go`) in a base between 2 and 36: the digits'
values, the parse of a string as a fold over its bytes, and its result (a number, or one of the
two errors it returns for such a base).
-/
module

public import Perennial.Proof.internal.strconv.Base

@[expose] public section

noncomputable section

namespace Perennial

namespace internal.strconv

/-- The value of the byte `c` as a digit in a base up to 36, as `ParseUint` reads it: `0`-`9`
are 0 to 9, a letter `a`-`z` or `A`-`Z` (`lower(c) = c | 0x20` between `'a'` and `'z'`) is 10 to
35; any other byte is none. -/
def digitVal (c : w8) : Option Nat :=
  if 48 ≤ uint.nat c ∧ uint.nat c ≤ 57 then some (uint.nat c - 48)
  else if 97 ≤ uint.nat (c ||| W8 32) ∧ uint.nat (c ||| W8 32) ≤ 122 then
    some (uint.nat (c ||| W8 32) - 97 + 10)
  else none

/-- What `ParseUint` returns, in a base between 2 and 36: a number, a syntax error (a byte that is
not a digit of the base, or an empty string) or a range error (the value exceeds the bit size's
maximum). -/
inductive ParseRes where
  | ok (n : Nat)
  | errSyntax
  | errRange
deriving DecidableEq

/-- `ParseUint`'s loop over the bytes `cs` from the value `n` read so far, in base `base` with
maximum `maxVal`: each byte is a digit below the base (else a syntax error), and the value after
it, `n * base + d`, is at most `maxVal` (else a range error, at the first byte that exceeds it,
even if a later byte is not a digit). -/
def parseDigits (base maxVal : Nat) : GoString → Nat → ParseRes
  | [], n => .ok n
  | c :: cs, n =>
    match digitVal c with
    | none => .errSyntax
    | some d =>
      if base ≤ d then .errSyntax
      else if maxVal < n * base + d then .errRange
      else parseDigits base maxVal cs (n * base + d)

/-- The bit size `ParseUint` uses: `bitSize`, or 64 (`IntSize`) for 0. -/
def effBitSize (bitSize : Nat) : Nat := if bitSize = 0 then 64 else bitSize

/-- `ParseUint(s, base, bitSize)` for a base between 2 and 36 and a bit size between 0 and 64:
a syntax error for the empty string, else the loop over `s` from 0 with the maximum
`2^bitSize - 1`. -/
def parseUint (s : GoString) (base bitSize : Nat) : ParseRes :=
  if s = [] then .errSyntax else parseDigits base (2 ^ effBitSize bitSize - 1) s 0

theorem parseDigits_cons_ok {base maxVal : Nat} {c : w8} {cs : GoString} {n d : Nat}
    (hd : digitVal c = some d) (hb : d < base) (hm : n * base + d ≤ maxVal) :
    parseDigits base maxVal (c :: cs) n = parseDigits base maxVal cs (n * base + d) := by
  simp only [parseDigits, hd, if_neg (show ¬ base ≤ d by omega),
    if_neg (show ¬ maxVal < n * base + d by omega)]

theorem parseDigits_cons_none {base maxVal : Nat} {c : w8} {cs : GoString} {n : Nat}
    (hd : digitVal c = none) : parseDigits base maxVal (c :: cs) n = .errSyntax := by
  simp only [parseDigits, hd]

theorem parseDigits_cons_ge {base maxVal : Nat} {c : w8} {cs : GoString} {n d : Nat}
    (hd : digitVal c = some d) (hb : base ≤ d) : parseDigits base maxVal (c :: cs) n = .errSyntax := by
  simp only [parseDigits, hd, if_pos hb]

theorem parseDigits_cons_range {base maxVal : Nat} {c : w8} {cs : GoString} {n d : Nat}
    (hd : digitVal c = some d) (hb : d < base) (hm : maxVal < n * base + d) :
    parseDigits base maxVal (c :: cs) n = .errRange := by
  simp only [parseDigits, hd, if_neg (show ¬ base ≤ d by omega), if_pos hm]

theorem parseUint_of_ne {s : GoString} (hs : s ≠ []) (base bitSize : Nat) :
    parseUint s base bitSize = parseDigits base (2 ^ effBitSize bitSize - 1) s 0 := by
  simp only [parseUint, if_neg hs]

/-- A string of digits below the base parses to its value when that value fits. -/
theorem parseDigits_append_ok {base maxVal : Nat} (p q : GoString) (n : Nat) :
    parseDigits base maxVal (p ++ q) n =
      match parseDigits base maxVal p n with
      | .ok m => parseDigits base maxVal q m
      | r => r := by
  induction p generalizing n with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.cons_append, parseDigits]
    cases digitVal c with
    | none => rfl
    | some d =>
      simp only
      by_cases h1 : base ≤ d
      · simp only [if_pos h1]
      · by_cases h2 : maxVal < n * base + d
        · simp only [if_neg h1, if_pos h2]
        · simp only [if_neg h1, if_neg h2]; exact ih _

/-- `1 << bs - 1` in `uint64`, for a bit size between 1 and 64 (`1 << 64` is 0 in Go). -/
theorem maxVal_eq (bs : w64) (h1 : 1 ≤ sint.Z bs) (h2 : sint.Z bs ≤ 64) :
    uint.nat (W64 1 <<< bs - W64 1) = 2 ^ sint.nat bs - 1 := by
  have hk : sint.nat bs = bs.toNat := by word
  have hk1 : 1 ≤ bs.toNat := by word
  have hk2 : bs.toNat ≤ 64 := by word
  rw [hk]
  show (W64 1 <<< bs - W64 1).toNat = 2 ^ bs.toNat - 1
  rw [BitVec.toNat_sub, BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft]
  have h1 : (W64 1).toNat = 1 := rfl
  rw [h1, Nat.shiftLeft_eq, Nat.one_mul]
  have hp : 2 ^ bs.toNat ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hk2
  have hp1 : 1 ≤ 2 ^ bs.toNat := Nat.one_le_two_pow
  rcases Nat.lt_or_eq_of_le hk2 with h | h
  · have hlt : 2 ^ bs.toNat < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) h
    rw [Nat.mod_eq_of_lt hlt]
    rw [show 2 ^ 64 - 1 + 2 ^ bs.toNat = 2 ^ 64 + (2 ^ bs.toNat - 1) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  · rw [h, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt (by decide)]

section out
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext]

/-- What `ParseUint` returns for the result `r`, the maximum being `maxVal`: the number and a nil
error; `0` and `ErrSyntax`; `maxVal` and `ErrRange` (each error an `internal/strconv.Error`
converted to `error`). -/
def parseOut (r : ParseRes) (maxVal : Nat) (x : w64) (err : GoInterface) : Prop :=
  match r with
  | .ok n => x = W64 n ∧ err = interface.nil
  | .errSyntax => x = W64 0 ∧ err = interface.mkOk Error.ty #(W64 2)
  | .errRange => x = W64 maxVal ∧ err = interface.mkOk Error.ty #(W64 1)

end out

end internal.strconv

end Perennial
