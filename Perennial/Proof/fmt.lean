/-
Package initialization of `fmt`, `fmt.Errorf`, `fmt.Sprintf` (with `SprintfOut`, the relation
its result satisfies, and the decimals its integer directives write) and `fmt.Printf`.
-/
module

public import Perennial.Proof.io
public import Perennial.Code.fmt
public import Perennial.GeneratedProof.fmt

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace fmt

/-! ## Decimals

What `%d`, `%v` and `%0Nd` write: `decimal z` and `decimalPad N z`, from the digits of a natural
number, `decimalNat`. Bytes are `w8`: `W8 48` is `0`, `W8 45` is `-`. -/

/-- The ASCII digit `'0' + d`, a digit for `d < 10`. -/
def digitByte (d : Nat) : w8 := W8 (48 + d)

/-- The decimal digits of `n`, most significant first, without leading zeros (`"0"` for `0`). -/
def decimalNat (n : Nat) : GoString :=
  (if n < 10 then [] else decimalNat (n / 10)) ++ [digitByte (n % 10)]
termination_by n
decreasing_by omega

/-- The decimal of `z`, with a leading `-` if `z` is negative: what `%d` and `%v` write. -/
def decimal (z : Int) : GoString :=
  if z < 0 then W8 45 :: decimalNat z.natAbs else decimalNat z.natAbs

/-- `s` with leading `'0'`s up to length `n` (`s` itself if it is at least that long). -/
def padZeros (n : Nat) (s : GoString) : GoString :=
  List.replicate (n - s.length) (W8 48) ++ s

/-- What `%0Nd` writes for `N = w`: the decimal of `z` with leading zeros up to width `w`, the
sign of a negative `z` before the zeros. -/
def decimalPad (w : Nat) (z : Int) : GoString :=
  if z < 0 then W8 45 :: padZeros (w - 1) (decimalNat z.natAbs)
  else padZeros w (decimalNat z.natAbs)

theorem decimalNat_eq (n : Nat) :
    decimalNat n = (if n < 10 then [] else decimalNat (n / 10)) ++ [digitByte (n % 10)] := by
  rw [decimalNat]

theorem decimalNat_of_lt {n : Nat} (h : n < 10) : decimalNat n = [digitByte n] := by
  rw [decimalNat_eq, ite_eq_left h, Nat.mod_eq_of_lt h]; rfl

theorem decimalNat_of_ge {n : Nat} (h : 10 ≤ n) :
    decimalNat n = decimalNat (n / 10) ++ [digitByte (n % 10)] := by
  rw [decimalNat_eq, ite_eq_right (by omega)]

theorem decimalNat_ne_nil (n : Nat) : decimalNat n ≠ [] := by
  rw [decimalNat_eq]; simp

theorem length_decimalNat_pos (n : Nat) : 0 < (decimalNat n).length :=
  List.length_pos_iff.mpr (decimalNat_ne_nil n)

/-- The decimal of `n < 10^k` has at most `k` digits (`k ≥ 1`). -/
theorem length_decimalNat_le (n k : Nat) (hk : 1 ≤ k) (h : n < 10 ^ k) :
    (decimalNat n).length ≤ k := by
  induction n using Nat.strongRecOn generalizing k with
  | _ n ih =>
    by_cases hn : n < 10
    · rw [decimalNat_of_lt hn]; simpa using hk
    · rw [decimalNat_of_ge (by omega)]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hk' : 1 ≤ k' := by
        rcases k' with _ | k'
        · simp at h; omega
        · omega
      have h' : n / 10 < 10 ^ k' := by
        rw [Nat.pow_succ] at h; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
      have := ih (n / 10) (by omega) k' hk' h'
      simp; omega

theorem digitByte_mem_range {d : Nat} (h : d < 10) :
    48 ≤ uint.Z (digitByte d) ∧ uint.Z (digitByte d) ≤ 57 := by
  unfold digitByte; constructor <;> word

/-- Every byte of a decimal is a digit, `'0'` to `'9'`. -/
theorem decimalNat_digits (n : Nat) :
    ∀ c ∈ decimalNat n, 48 ≤ uint.Z c ∧ uint.Z c ≤ 57 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro c hc
    rw [decimalNat_eq] at hc
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · split at hc
      · simp at hc
      · exact ih (n / 10) (by omega) c hc
    · exact digitByte_mem_range (Nat.mod_lt _ (by omega))

theorem length_padZeros (n : Nat) (s : GoString) :
    (padZeros n s).length = max n s.length := by
  simp [padZeros]; omega

theorem padZeros_of_le {n : Nat} {s : GoString} (h : n ≤ s.length) : padZeros n s = s := by
  simp [padZeros, Nat.sub_eq_zero_of_le h]

theorem decimal_of_nonneg {z : Int} (h : 0 ≤ z) : decimal z = decimalNat z.toNat := by
  simp only [decimal, show ¬ z < 0 by omega, ↓reduceIte]
  congr 1; omega

theorem decimal_natCast (n : Nat) : decimal (n : Int) = decimalNat n := by
  simp [decimal]

theorem decimalPad_of_nonneg {z : Int} (w : Nat) (h : 0 ≤ z) :
    decimalPad w z = padZeros w (decimal z) := by
  simp only [decimalPad, decimal, show ¬ z < 0 by omega, ↓reduceIte]

theorem decimalPad_zero (z : Int) : decimalPad 0 z = decimal z := by
  unfold decimalPad decimal padZeros
  split <;> simp

/-! The order of zero-padded decimals. -/

/-- The last `k` decimal digits of `n`, most significant first. -/
def fixedDigits : Nat → Nat → GoString
  | 0, _ => []
  | k + 1, n => digitByte (n / 10 ^ k % 10) :: fixedDigits k n

theorem fixedDigits_zero (k : Nat) : fixedDigits k 0 = List.replicate k (W8 48) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [fixedDigits, ih, List.replicate_succ, digitByte]

theorem fixedDigits_succ_snoc (k n : Nat) :
    fixedDigits (k + 1) n = fixedDigits k (n / 10) ++ [digitByte (n % 10)] := by
  induction k with
  | zero => simp [fixedDigits]
  | succ k ih =>
    rw [fixedDigits, ih, fixedDigits, Nat.div_div_eq_div_mul, ← Nat.pow_succ']
    rfl

theorem padZeros_decimalNat (k n : Nat) (h : n < 10 ^ (k + 1)) :
    padZeros (k + 1) (decimalNat n) = fixedDigits (k + 1) n := by
  induction k generalizing n with
  | zero =>
    simp at h
    rw [decimalNat_of_lt h, padZeros_of_le (by simp)]
    simp [fixedDigits, Nat.mod_eq_of_lt h]
  | succ k ih =>
    rw [fixedDigits_succ_snoc]
    by_cases hn : n < 10
    · rw [decimalNat_of_lt hn, Nat.div_eq_of_lt hn, fixedDigits_zero]
      simp [padZeros, Nat.mod_eq_of_lt hn, List.replicate_succ]
    · rw [decimalNat_of_ge (by omega)]
      have h' : n / 10 < 10 ^ (k + 1) := by
        rw [Nat.pow_succ] at h; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
      rw [← ih (n / 10) h']
      have := length_decimalNat_le (n / 10) (k + 1) (by omega) h'
      simp only [padZeros, List.length_append, List.length_singleton, List.append_assoc]
      congr 2
      omega

theorem fixedDigits_lt (k : Nat) :
    ∀ a b : Nat, a % 10 ^ k < b % 10 ^ k → go.GoStringLt (fixedDigits k a) (fixedDigits k b) := by
  induction k with
  | zero => intro a b h; simp [Nat.mod_one] at h
  | succ k ih =>
    intro a b h
    rw [Nat.mod_pow_succ, Nat.mod_pow_succ] at h
    have ha : a % 10 ^ k < 10 ^ k := Nat.mod_lt _ (Nat.pow_pos (by omega))
    have hb : b % 10 ^ k < 10 ^ k := Nat.mod_lt _ (Nat.pow_pos (by omega))
    have hda : a / 10 ^ k % 10 < 10 := Nat.mod_lt _ (by omega)
    have hdb : b / 10 ^ k % 10 < 10 := Nat.mod_lt _ (by omega)
    simp only [fixedDigits]
    by_cases hd : a / 10 ^ k % 10 < b / 10 ^ k % 10
    · apply List.Lex.rel
      unfold digitByte; word
    · have heq : a / 10 ^ k % 10 = b / 10 ^ k % 10 := by
        rcases Nat.lt_or_ge (b / 10 ^ k % 10) (a / 10 ^ k % 10) with h' | h'
        · exfalso
          have : 10 ^ k * (b / 10 ^ k % 10 + 1) ≤ 10 ^ k * (a / 10 ^ k % 10) :=
            Nat.mul_le_mul_left _ h'
          rw [Nat.mul_add, Nat.mul_one] at this
          omega
        · omega
      rw [heq]
      apply List.Lex.cons
      apply ih
      rw [heq] at h
      omega

/-- Zero-padded decimals of width `N` compare as the numbers: for `a < b < 10^N`, the bytes of
`%0Nd` of `a` are lexicographically less than those of `b` (`go.GoStringLt`, the order of
`strings.Compare` and `bytes.Compare`). -/
theorem padZeros_decimalNat_lt (N a b : Nat) (hab : a < b) (hb : b < 10 ^ N) :
    go.GoStringLt (padZeros N (decimalNat a)) (padZeros N (decimalNat b)) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by rcases N with _ | N <;> simp at hb ⊢; omega⟩
  rw [padZeros_decimalNat k a (by omega), padZeros_decimalNat k b hb]
  apply fixedDigits_lt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hb]
  exact hab

/-- `padZeros_decimalNat_lt` for integers: for `0 ≤ a < b < 10^N`, `%0Nd` of `a` is
lexicographically less than `%0Nd` of `b`. -/
theorem padZeros_decimal_lt (N : Nat) (a b : Int) (ha : 0 ≤ a) (hab : a < b)
    (hb : b < 10 ^ N) :
    go.GoStringLt (padZeros N (decimal a)) (padZeros N (decimal b)) := by
  rw [decimal_of_nonneg ha, decimal_of_nonneg (by omega)]
  have h10 : ((10 ^ N : Nat) : Int) = 10 ^ N := Int.natCast_pow 10 N
  exact padZeros_decimalNat_lt N _ _ (by omega) (by omega)

/-! ## The output of `Sprintf`

`SprintfOut format args out`: `out` is a possible result of the model of `Sprintf`
(`Perennial/TrustedCode/fmt.lean`) on `format` and the arguments `args`. Bytes are `w8`:
`W8 37` is `%`, `W8 115` is `s`, `W8 100` is `d`, `W8 118` is `v`, `W8 48` is `0`. -/

/-- The width of `%0Nd` read from `f` (after the `0`) with `w` read so far, and the rest of `f`:
digits are read while the width so far is at most `10^6`, as in the model's `intVerb`. -/
def scanWidth (w : Nat) : GoString → Nat × GoString
  | [] => (w, [])
  | c :: r =>
    if 48 ≤ uint.Z c ∧ uint.Z c ≤ 57 ∧ w ≤ 1000000 then scanWidth (w * 10 + (uint.nat c - 48)) r
    else (w, c :: r)

/-- The integer directive at the start of `f` (the format after a `%`), as the model's `intVerb`
reads it: its width and the rest of the format. `%d` and `%v` have width 0; `%0Nd` has a
width `N` of one or more digits, at most `10^6`. -/
def parseIntVerb : GoString → Option (Nat × GoString)
  | [] => none
  | c :: f =>
    if c = W8 100 ∨ c = W8 118 then some (0, f)
    else if c = W8 48 then
      match scanWidth 0 f with
      | (w, d :: rest) =>
        if (d :: rest).length < f.length ∧ d = W8 100 ∧ w ≤ 1000000 then some (w, rest) else none
      | (_, []) => none
    else none

/-! Tests of `parseIntVerb`. -/

example : parseIntVerb go!"d" = some (0, []) := by decide
example : parseIntVerb go!"v/x" = some (0, go!"/x") := by decide
example : parseIntVerb go!"05d" = some (5, []) := by decide
example : parseIntVerb go!"016dx" = some (16, go!"x") := by decide
example : parseIntVerb go!"0d" = none := by decide
example : parseIntVerb go!"05v" = none := by decide
example : parseIntVerb go!"5d" = none := by decide

/-- One of Go's ten (predeclared) integer types, which the model of `Sprintf` formats. -/
def IsIntType [FfiSyntax] (t : go.GoType) : Prop :=
  t = go.int ∨ t = go.int64 ∨ t = go.int32 ∨ t = go.int16 ∨ t = go.int8 ∨
  t = go.uint ∨ t = go.uint64 ∨ t = go.uint32 ∨ t = go.uint16 ∨ t = go.uint8

/-- `IntArgValue ii z`: the interface `ii` holds the integer `z`, of one of Go's integer types
(signed for `int`, ..., `int8`, unsigned for `uint`, ..., `uint8`). -/
inductive IntArgValue [FfiSyntax] [GoGlobalContext] : GoInterfaceOk → Int → Prop
  | int (n : w64) : IntArgValue (interface.mk go.int #n) (sint.Z n)
  | int64 (n : w64) : IntArgValue (interface.mk go.int64 #n) (sint.Z n)
  | int32 (n : w32) : IntArgValue (interface.mk go.int32 #n) (sint.Z n)
  | int16 (n : w16) : IntArgValue (interface.mk go.int16 #n) (sint.Z n)
  | int8 (n : w8) : IntArgValue (interface.mk go.int8 #n) (sint.Z n)
  | uint (n : w64) : IntArgValue (interface.mk go.uint #n) (uint.Z n)
  | uint64 (n : w64) : IntArgValue (interface.mk go.uint64 #n) (uint.Z n)
  | uint32 (n : w32) : IntArgValue (interface.mk go.uint32 #n) (uint.Z n)
  | uint16 (n : w16) : IntArgValue (interface.mk go.uint16 #n) (uint.Z n)
  | uint8 (n : w8) : IntArgValue (interface.mk go.uint8 #n) (uint.Z n)

theorem IntArgValue.cast [FfiSyntax] [GoGlobalContext] {ii : GoInterfaceOk} {z z' : Int}
    (h : IntArgValue ii z) (e : z = z') : IntArgValue ii z' := e ▸ h

/-! Inversions of `IntArgValue`: the value of an interface of an integer type. -/

theorem IntArgValue.of_int [FfiSyntax] [GoGlobalContext] {v : val} {z : Int}
    (h : IntArgValue (interface.mk go.int v) z) : ∃ n : w64, v = #n ∧ z = sint.Z n := by
  generalize hii : interface.mk go.int v = ii at h
  cases h <;> simp only [GoInterfaceOk.mk.injEq] at hii <;> obtain ⟨hty, rfl⟩ := hii <;>
    first | exact ⟨_, rfl, rfl⟩ | (exfalso; simp [go.int, go.int32, go.int16, go.int8, go.uint, go.uint64, go.uint32, go.uint16, go.uint8] at hty)

theorem IntArgValue.of_int64 [FfiSyntax] [GoGlobalContext] {v : val} {z : Int}
    (h : IntArgValue (interface.mk go.int64 v) z) : ∃ n : w64, v = #n ∧ z = sint.Z n := by
  generalize hii : interface.mk go.int64 v = ii at h
  cases h <;> simp only [GoInterfaceOk.mk.injEq] at hii <;> obtain ⟨hty, rfl⟩ := hii <;>
    first | exact ⟨_, rfl, rfl⟩ | (exfalso; simp [go.int64, go.int32, go.int16, go.int8, go.uint, go.uint64, go.uint32, go.uint16, go.uint8] at hty)

theorem IntArgValue.of_int32 [FfiSyntax] [GoGlobalContext] {v : val} {z : Int}
    (h : IntArgValue (interface.mk go.int32 v) z) : ∃ n : w32, v = #n ∧ z = sint.Z n := by
  generalize hii : interface.mk go.int32 v = ii at h
  cases h <;> simp only [GoInterfaceOk.mk.injEq] at hii <;> obtain ⟨hty, rfl⟩ := hii <;>
    first | exact ⟨_, rfl, rfl⟩ | (exfalso; simp [go.int, go.int64, go.int32, go.int16, go.int8, go.uint, go.uint64, go.uint32, go.uint16, go.uint8] at hty)

theorem IntArgValue.of_int16 [FfiSyntax] [GoGlobalContext] {v : val} {z : Int}
    (h : IntArgValue (interface.mk go.int16 v) z) : ∃ n : w16, v = #n ∧ z = sint.Z n := by
  generalize hii : interface.mk go.int16 v = ii at h
  cases h <;> simp only [GoInterfaceOk.mk.injEq] at hii <;> obtain ⟨hty, rfl⟩ := hii <;>
    first | exact ⟨_, rfl, rfl⟩ | (exfalso; simp [go.int, go.int64, go.int32, go.int16, go.int8, go.uint, go.uint64, go.uint32, go.uint16, go.uint8] at hty)

theorem IntArgValue.of_int8 [FfiSyntax] [GoGlobalContext] {v : val} {z : Int}
    (h : IntArgValue (interface.mk go.int8 v) z) : ∃ n : w8, v = #n ∧ z = sint.Z n := by
  generalize hii : interface.mk go.int8 v = ii at h
  cases h <;> simp only [GoInterfaceOk.mk.injEq] at hii <;> obtain ⟨hty, rfl⟩ := hii <;>
    first | exact ⟨_, rfl, rfl⟩ | (exfalso; simp [go.int, go.int64, go.int32, go.int16, go.int8, go.uint, go.uint64, go.uint32, go.uint16, go.uint8] at hty)

theorem IntArgValue.of_uint [FfiSyntax] [GoGlobalContext] {v : val} {z : Int}
    (h : IntArgValue (interface.mk go.uint v) z) : ∃ n : w64, v = #n ∧ z = uint.Z n := by
  generalize hii : interface.mk go.uint v = ii at h
  cases h <;> simp only [GoInterfaceOk.mk.injEq] at hii <;> obtain ⟨hty, rfl⟩ := hii <;>
    first | exact ⟨_, rfl, rfl⟩ | (exfalso; simp [go.int, go.int64, go.int32, go.int16, go.int8, go.uint, go.uint32, go.uint16, go.uint8] at hty)

theorem IntArgValue.of_uint64 [FfiSyntax] [GoGlobalContext] {v : val} {z : Int}
    (h : IntArgValue (interface.mk go.uint64 v) z) : ∃ n : w64, v = #n ∧ z = uint.Z n := by
  generalize hii : interface.mk go.uint64 v = ii at h
  cases h <;> simp only [GoInterfaceOk.mk.injEq] at hii <;> obtain ⟨hty, rfl⟩ := hii <;>
    first | exact ⟨_, rfl, rfl⟩ | (exfalso; simp [go.int, go.int64, go.int32, go.int16, go.int8, go.uint64, go.uint32, go.uint16, go.uint8] at hty)

theorem IntArgValue.of_uint32 [FfiSyntax] [GoGlobalContext] {v : val} {z : Int}
    (h : IntArgValue (interface.mk go.uint32 v) z) : ∃ n : w32, v = #n ∧ z = uint.Z n := by
  generalize hii : interface.mk go.uint32 v = ii at h
  cases h <;> simp only [GoInterfaceOk.mk.injEq] at hii <;> obtain ⟨hty, rfl⟩ := hii <;>
    first | exact ⟨_, rfl, rfl⟩ | (exfalso; simp [go.int, go.int64, go.int32, go.int16, go.int8, go.uint, go.uint64, go.uint32, go.uint16, go.uint8] at hty)

theorem IntArgValue.of_uint16 [FfiSyntax] [GoGlobalContext] {v : val} {z : Int}
    (h : IntArgValue (interface.mk go.uint16 v) z) : ∃ n : w16, v = #n ∧ z = uint.Z n := by
  generalize hii : interface.mk go.uint16 v = ii at h
  cases h <;> simp only [GoInterfaceOk.mk.injEq] at hii <;> obtain ⟨hty, rfl⟩ := hii <;>
    first | exact ⟨_, rfl, rfl⟩ | (exfalso; simp [go.int, go.int64, go.int32, go.int16, go.int8, go.uint, go.uint64, go.uint32, go.uint16, go.uint8] at hty)

theorem IntArgValue.of_uint8 [FfiSyntax] [GoGlobalContext] {v : val} {z : Int}
    (h : IntArgValue (interface.mk go.uint8 v) z) : ∃ n : w8, v = #n ∧ z = uint.Z n := by
  generalize hii : interface.mk go.uint8 v = ii at h
  cases h <;> simp only [GoInterfaceOk.mk.injEq] at hii <;> obtain ⟨hty, rfl⟩ := hii <;>
    first | exact ⟨_, rfl, rfl⟩ | (exfalso; simp [go.int, go.int64, go.int32, go.int16, go.int8, go.uint, go.uint64, go.uint32, go.uint16, go.uint8] at hty)

/-- At `%` followed by `f`, with arguments `args` left: whether the model formats the directive
(`%%`, `%s` of an interface holding a `string`, or an integer directive, `parseIntVerb`, of an
interface holding an integer); at any other directive the rest of the output is arbitrary. -/
def SimpleDirective [FfiSyntax] : GoString → List GoInterface → Prop
  | c :: f, args =>
      c = W8 37 ∨ (c = W8 115 ∧ ∃ ii rest, args = interface.ok ii :: rest ∧ ii.ty = go.string) ∨
      ((parseIntVerb (c :: f)).isSome ∧ ∃ ii rest, args = interface.ok ii :: rest ∧ IsIntType ii.ty)
  | [], _ => False

/-- `SprintfOut format args out`: `out` is a possible result of `fmt.Sprintf(format, args...)`,
as the model of `Sprintf` formats it. Bytes other than `%` are copied, `%%` gives `%`, `%s` with
an interface holding a `string` next gives that string, `%d`, `%v` and `%0Nd` with an interface
holding an integer next give its (zero-padded) decimal; at any other directive, and after the
format if arguments remain unused, the rest of the output is arbitrary. -/
inductive SprintfOut [FfiSyntax] [GoGlobalContext] :
    GoString → List GoInterface → GoString → Prop
  /-- The end of the format, every argument used: nothing more. -/
  | done : SprintfOut [] [] []
  /-- The end of the format, arguments unused: an arbitrary suffix (Go's `%!(EXTRA ...)`). -/
  | extra (a : GoInterface) (args : List GoInterface) (junk : GoString) :
      SprintfOut [] (a :: args) junk
  /-- A byte other than `%` is copied. -/
  | byte (c : w8) (f : GoString) (args : List GoInterface) (out : GoString) :
      c ≠ W8 37 → SprintfOut f args out → SprintfOut (c :: f) args (c :: out)
  /-- `%%` gives `%`. -/
  | percent (f : GoString) (args : List GoInterface) (out : GoString) :
      SprintfOut f args out → SprintfOut (W8 37 :: W8 37 :: f) args (W8 37 :: out)
  /-- `%s` of an interface holding the string `x` gives `x`, and consumes the argument. -/
  | str (x : GoString) (f : GoString) (args : List GoInterface) (out : GoString) :
      SprintfOut f args out →
      SprintfOut (W8 37 :: W8 115 :: f) (interface.mkOk go.string #x :: args) (x ++ out)
  /-- An integer directive of width `w` (`%d`, `%v`: 0; `%0Nd`: `N`) of an interface holding the
  integer `z` gives `decimalPad w z`, and consumes the argument. -/
  | int (f rest : GoString) (w : Nat) (ii : GoInterfaceOk) (z : Int) (args : List GoInterface)
      (out : GoString) :
      parseIntVerb f = some (w, rest) → IntArgValue ii z → SprintfOut rest args out →
      SprintfOut (W8 37 :: f) (interface.ok ii :: args) (decimalPad w z ++ out)
  /-- Any other directive (or a trailing lone `%`): the rest of the output is arbitrary. -/
  | other (f : GoString) (args : List GoInterface) (junk : GoString) :
      ¬ SimpleDirective f args → SprintfOut (W8 37 :: f) args junk

/-- The arguments' dynamic types tell the truth about `string`s: an argument whose dynamic type
is `string` holds a string. (Go's typing guarantees it; a `GoInterface` does not.) -/
def StringArgsWf [FfiSyntax] [GoGlobalContext] (args : List GoInterface) : Prop :=
  ∀ ii, interface.ok ii ∈ args → ii.ty = go.string → ∃ x : GoString, ii.v = #x

/-- One of Go's predeclared basic types (`string`, `bool`, the integer, floating-point and
complex types). These have no methods, so Go's formatting of such an argument calls no
`Error()`, `String()`, `Format` or `GoString` method: the models of `Sprintf`, `Errorf` and
`Printf`, which never call an argument's methods, are faithful only for such arguments. (A
named type, even one whose underlying type is basic, is not a predeclared type: `go.int` is
`go.Named "int" []`.) -/
def IsBasicType [FfiSyntax] (t : go.GoType) : Prop :=
  t = go.string ∨ t = go.bool ∨ IsIntType t ∨ t = go.uintptr ∨ t = go.float32 ∨
  t = go.float64 ∨ t = go.complex64 ∨ t = go.complex128

/-- An argument's dynamic type tells the truth about its value, for the types the model of
`Sprintf` formats: a `string` holds a string, an integer type an integer of its size (Go's
typing guarantees it; a `GoInterface` does not); and the type is a predeclared basic type
(`IsBasicType`), so that Go calls no method of the argument while formatting it. -/
def ArgWf [FfiSyntax] [GoGlobalContext] (ii : GoInterfaceOk) : Prop :=
  (ii.ty = go.string → ∃ x : GoString, ii.v = #x) ∧ (IsIntType ii.ty → ∃ z, IntArgValue ii z) ∧
  IsBasicType ii.ty

/-- Every argument is `nil` or well-formed (`ArgWf`): what `wp_Sprintf`, `wp_Errorf` and
`wp_Printf` need of the arguments. -/
def ArgsWf [FfiSyntax] [GoGlobalContext] (args : List GoInterface) : Prop :=
  ∀ ii, interface.ok ii ∈ args → ArgWf ii

section prefix_lemmas
variable [FfiSyntax] [GoGlobalContext]

theorem StringArgsWf.nil : StringArgsWf ([] : List GoInterface) := by
  intro ii h; simp at h

theorem StringArgsWf.cons_string (x : GoString) (args : List GoInterface)
    (h : StringArgsWf args) : StringArgsWf (interface.mkOk go.string #x :: args) := by
  intro ii hmem hty
  rcases List.mem_cons.mp hmem with heq | hmem
  · cases heq; exact ⟨x, rfl⟩
  · exact h ii hmem hty

theorem StringArgsWf.cons_other (t : go.GoType) (v : val) (args : List GoInterface)
    (ht : t ≠ go.string) (h : StringArgsWf args) :
    StringArgsWf (interface.mkOk t v :: args) := by
  intro ii hmem hty
  rcases List.mem_cons.mp hmem with heq | hmem
  · cases heq; exact absurd hty ht
  · exact h ii hmem hty

/-- `Sprintf("%s" + f, x, ...)` begins with `x`. -/
theorem SprintfOut.str_prefix [go.IntoValInj GoString] (x f : GoString)
    (args : List GoInterface) (out : GoString)
    (h : SprintfOut (go!"%s" ++ f) (interface.mkOk go.string #x :: args) out) : x <+: out := by
  have hfmt : go!"%s" ++ f = W8 37 :: W8 115 :: f := rfl
  rw [hfmt] at h
  generalize hF : (W8 37 :: W8 115 :: f) = F at h
  generalize hA : (interface.mkOk go.string #x :: args) = A at h
  cases h with
  | done => cases hF
  | extra => cases hF
  | byte c _ _ _ hc _ =>
    simp only [List.cons.injEq] at hF
    exact absurd hF.1.symm hc
  | percent =>
    simp only [List.cons.injEq] at hF
    exact absurd hF.2.1 (by decide)
  | str y _ _ out' _ =>
    simp only [List.cons.injEq, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at hA
    rw [go.intoVal_inj hA.1]
    exact ⟨out', rfl⟩
  | int f' _ _ _ _ _ _ hp =>
    simp only [List.cons.injEq] at hF
    obtain ⟨-, rfl⟩ := hF
    simp [parseIntVerb] at hp
  | other _ _ _ hnot =>
    simp only [List.cons.injEq] at hF
    obtain ⟨-, rfl⟩ := hF
    subst hA
    exact absurd (Or.inr (Or.inl ⟨rfl, _, _, rfl, rfl⟩)) hnot

/-- `Sprintf("%s%x", x, n)` begins with `x` (whatever the second argument). -/
theorem SprintfOut.str_x_prefix [go.IntoValInj GoString] (x : GoString)
    (args : List GoInterface) (out : GoString)
    (h : SprintfOut go!"%s%x" (interface.mkOk go.string #x :: args) out) : x <+: out :=
  SprintfOut.str_prefix x go!"%x" args out h

/-! `ArgsWf` of argument lists. -/

theorem IntArgValue.isIntType {ii : GoInterfaceOk} {z : Int} (h : IntArgValue ii z) :
    IsIntType ii.ty := by
  cases h <;> simp [IsIntType]

theorem ArgsWf.nil : ArgsWf ([] : List GoInterface) := by
  intro ii h; simp at h

theorem ArgsWf.cons_string (x : GoString) (args : List GoInterface) (h : ArgsWf args) :
    ArgsWf (interface.mkOk go.string #x :: args) := by
  intro ii hmem
  rcases List.mem_cons.mp hmem with heq | hmem
  · cases heq
    exact ⟨fun _ => ⟨x, rfl⟩, fun hi => by simp [IsIntType, go.string, go.int, go.int64, go.int32, go.int16, go.int8, go.uint, go.uint64, go.uint32, go.uint16, go.uint8] at hi,
      Or.inl rfl⟩
  · exact h ii hmem

theorem ArgsWf.cons_int (ii : GoInterfaceOk) (z : Int) (args : List GoInterface)
    (hz : IntArgValue ii z) (h : ArgsWf args) : ArgsWf (interface.ok ii :: args) := by
  intro ii' hmem
  rcases List.mem_cons.mp hmem with heq | hmem
  · cases heq
    refine ⟨fun hs => ?_, fun _ => ⟨z, hz⟩, Or.inr (Or.inr (Or.inl hz.isIntType))⟩
    exfalso
    cases hz <;> simp [go.string, go.int, go.int64, go.int32, go.int16, go.int8, go.uint, go.uint64, go.uint32, go.uint16, go.uint8] at hs
  · exact h ii' hmem

theorem ArgsWf.cons_other (t : go.GoType) (v : val) (args : List GoInterface)
    (hs : t ≠ go.string) (hi : ¬ IsIntType t) (hb : IsBasicType t) (h : ArgsWf args) :
    ArgsWf (interface.mkOk t v :: args) := by
  intro ii hmem
  rcases List.mem_cons.mp hmem with heq | hmem
  · cases heq; exact ⟨fun h' => absurd h' hs, fun h' => absurd h' hi, hb⟩
  · exact h ii hmem

theorem ArgsWf.cons_nil (args : List GoInterface) (h : ArgsWf args) :
    ArgsWf (interface.nil :: args) := by
  intro ii hmem
  rcases List.mem_cons.mp hmem with heq | hmem
  · cases heq
  · exact h ii hmem

theorem ArgsWf.stringArgsWf {args : List GoInterface} (h : ArgsWf args) : StringArgsWf args :=
  fun ii hmem hty => (h ii hmem).1 hty

/-! Inversions of `SprintfOut`, to compute the output of a given format. -/

theorem SprintfOut.done_inv {out : GoString} (h : SprintfOut [] [] out) : out = [] := by
  cases h
  rfl

theorem SprintfOut.byte_inv {c : w8} {f : GoString} {args : List GoInterface} {out : GoString}
    (hc : c ≠ W8 37) (h : SprintfOut (c :: f) args out) :
    ∃ out', out = c :: out' ∧ SprintfOut f args out' := by
  generalize hF : c :: f = F at h
  cases h with
  | done => cases hF
  | extra => cases hF
  | byte c' f' _ out' _ h' =>
    simp only [List.cons.injEq] at hF
    obtain ⟨rfl, rfl⟩ := hF
    exact ⟨out', rfl, h'⟩
  | percent => simp only [List.cons.injEq] at hF; exact absurd hF.1 hc
  | str => simp only [List.cons.injEq] at hF; exact absurd hF.1 hc
  | int => simp only [List.cons.injEq] at hF; exact absurd hF.1 hc
  | other => simp only [List.cons.injEq] at hF; exact absurd hF.1 hc

theorem SprintfOut.str_inv [go.IntoValInj GoString] {x f : GoString} {args : List GoInterface}
    {out : GoString}
    (h : SprintfOut (W8 37 :: W8 115 :: f) (interface.mkOk go.string #x :: args) out) :
    ∃ out', out = x ++ out' ∧ SprintfOut f args out' := by
  generalize hF : W8 37 :: W8 115 :: f = F at h
  generalize hA : interface.mkOk go.string #x :: args = A at h
  cases h with
  | done => cases hF
  | extra => cases hF
  | byte _ _ _ _ hc _ =>
    simp only [List.cons.injEq] at hF
    exact absurd hF.1.symm hc
  | percent =>
    simp only [List.cons.injEq] at hF
    exact absurd hF.2.1 (by decide)
  | str y f' args' out' h' =>
    simp only [List.cons.injEq] at hF hA
    obtain ⟨-, -, rfl⟩ := hF
    simp only [GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at hA
    obtain ⟨hxy, rfl⟩ := hA
    rw [go.intoVal_inj hxy]
    exact ⟨out', rfl, h'⟩
  | int f' _ _ _ _ _ _ hp =>
    simp only [List.cons.injEq] at hF
    obtain ⟨-, rfl⟩ := hF
    simp [parseIntVerb] at hp
  | other _ _ _ hnot =>
    simp only [List.cons.injEq] at hF
    obtain ⟨-, rfl⟩ := hF
    subst hA
    exact absurd (Or.inr (Or.inl ⟨rfl, _, _, rfl, rfl⟩)) hnot

theorem SprintfOut.int_inv {f rest : GoString} {w : Nat} {ii : GoInterfaceOk} {z : Int}
    {args : List GoInterface} {out : GoString}
    (hp : parseIntVerb f = some (w, rest)) (hz : IntArgValue ii z)
    (huniq : ∀ z', IntArgValue ii z' → z' = z)
    (h : SprintfOut (W8 37 :: f) (interface.ok ii :: args) out) :
    ∃ out', out = decimalPad w z ++ out' ∧ SprintfOut rest args out' := by
  generalize hF : W8 37 :: f = F at h
  generalize hA : interface.ok ii :: args = A at h
  cases h with
  | done => cases hF
  | extra => cases hF
  | byte _ _ _ _ hc _ =>
    simp only [List.cons.injEq] at hF
    exact absurd hF.1.symm hc
  | percent f' =>
    simp only [List.cons.injEq] at hF
    obtain ⟨-, rfl⟩ := hF
    simp [parseIntVerb] at hp
  | str y f' =>
    simp only [List.cons.injEq] at hF
    obtain ⟨-, rfl⟩ := hF
    simp [parseIntVerb] at hp
  | int f' rest' w' ii' z' args' out' hp' hz' h' =>
    simp only [List.cons.injEq] at hF hA
    obtain ⟨-, rfl⟩ := hF
    obtain ⟨hii, rfl⟩ := hA
    cases hii
    rw [hp] at hp'
    simp only [Option.some.injEq, Prod.mk.injEq] at hp'
    obtain ⟨rfl, rfl⟩ := hp'
    rw [huniq z' hz']
    exact ⟨out', rfl, h'⟩
  | other _ _ _ hnot =>
    simp only [List.cons.injEq] at hF
    obtain ⟨-, rfl⟩ := hF
    subst hA
    refine absurd ?_ hnot
    cases f with
    | nil => simp [parseIntVerb] at hp
    | cons c f =>
      exact Or.inr (Or.inr ⟨by rw [hp]; rfl, _, _, rfl, hz.isIntType⟩)

theorem IntArgValue.uniq_int64 [go.IntoValInj w64] (n : w64) :
    ∀ z', IntArgValue (interface.mk go.int64 #n) z' → z' = sint.Z n := by
  intro z' h
  obtain ⟨n', hv, rfl⟩ := IntArgValue.of_int64 h
  rw [go.intoVal_inj hv]

theorem IntArgValue.uniq_int [go.IntoValInj w64] (n : w64) :
    ∀ z', IntArgValue (interface.mk go.int #n) z' → z' = sint.Z n := by
  intro z' h
  obtain ⟨n', hv, rfl⟩ := IntArgValue.of_int h
  rw [go.intoVal_inj hv]

theorem IntArgValue.uniq_uint16 [go.IntoValInj w16] (n : w16) :
    ∀ z', IntArgValue (interface.mk go.uint16 #n) z' → z' = uint.Z n := by
  intro z' h
  obtain ⟨n', hv, rfl⟩ := IntArgValue.of_uint16 h
  rw [go.intoVal_inj hv]

/-- `Sprintf("%s/%v", x, n)` for a string `x` and an `int64` `n` is exactly `x/n`, `n` in decimal. -/
theorem SprintfOut.str_slash_v_int64 [go.IntoValInj GoString] [go.IntoValInj w64]
    (x : GoString) (n : w64) (out : GoString)
    (h : SprintfOut go!"%s/%v" [interface.mkOk go.string #x, interface.mkOk go.int64 #n] out) :
    out = x ++ go!"/" ++ decimal (sint.Z n) := by
  have hfmt : go!"%s/%v" = W8 37 :: W8 115 :: W8 47 :: W8 37 :: [W8 118] := rfl
  rw [hfmt] at h
  obtain ⟨o1, rfl, h1⟩ := SprintfOut.str_inv h
  obtain ⟨o2, rfl, h2⟩ := SprintfOut.byte_inv (by decide) h1
  obtain ⟨o3, rfl, h3⟩ := SprintfOut.int_inv (w := 0) (rest := []) (by decide) (IntArgValue.int64 n)
    (IntArgValue.uniq_int64 n) h2
  rw [SprintfOut.done_inv h3, decimalPad_zero]
  simp

/-- `Sprintf("%s%05d", x, n)` for a string `x` and a `uint16` `n` is exactly `x` then `n` in
decimal with leading zeros up to 5 digits. -/
theorem SprintfOut.str_05d_uint16 [go.IntoValInj GoString] [go.IntoValInj w16]
    (x : GoString) (n : w16) (out : GoString)
    (h : SprintfOut go!"%s%05d" [interface.mkOk go.string #x, interface.mkOk go.uint16 #n] out) :
    out = x ++ padZeros 5 (decimal (uint.Z n)) := by
  have hfmt : go!"%s%05d" = W8 37 :: W8 115 :: W8 37 :: [W8 48, W8 53, W8 100] := rfl
  rw [hfmt] at h
  obtain ⟨o1, rfl, h1⟩ := SprintfOut.str_inv h
  obtain ⟨o2, rfl, h2⟩ := SprintfOut.int_inv (w := 5) (rest := []) (by decide) (IntArgValue.uint16 n)
    (IntArgValue.uniq_uint16 n) h1
  rw [SprintfOut.done_inv h2, decimalPad_of_nonneg _ (by word)]
  simp

/-- `Sprintf("%s/%016d", x, n)` for a string `x` and a non-negative `int` `n` is exactly `x/` then
`n` in decimal with leading zeros up to 16 digits. -/
theorem SprintfOut.str_slash_016d_int [go.IntoValInj GoString] [go.IntoValInj w64]
    (x : GoString) (n : w64) (hn : 0 ≤ sint.Z n) (out : GoString)
    (h : SprintfOut go!"%s/%016d" [interface.mkOk go.string #x, interface.mkOk go.int #n] out) :
    out = x ++ go!"/" ++ padZeros 16 (decimal (sint.Z n)) := by
  have hfmt : go!"%s/%016d" =
      W8 37 :: W8 115 :: W8 47 :: W8 37 :: [W8 48, W8 49, W8 54, W8 100] := rfl
  rw [hfmt] at h
  obtain ⟨o1, rfl, h1⟩ := SprintfOut.str_inv h
  obtain ⟨o2, rfl, h2⟩ := SprintfOut.byte_inv (by decide) h1
  obtain ⟨o3, rfl, h3⟩ := SprintfOut.int_inv (w := 16) (rest := []) (by decide) (IntArgValue.int n)
    (IntArgValue.uniq_int n) h2
  rw [SprintfOut.done_inv h3, decimalPad_of_nonneg _ hn]
  simp

/-! Tests of `SprintfOut`, `ArgsWf` and the decimals. -/

example (pfx : GoString) (n : w64) :
    StringArgsWf [interface.mkOk go.string #pfx, interface.mkOk go.int64 #n] :=
  .cons_string _ _ (.cons_other _ _ _ (by simp [go.int64, go.string]) .nil)

example (pfx : GoString) (n : w64) :
    ArgsWf [interface.mkOk go.string #pfx, interface.mkOk go.int64 #n] :=
  .cons_string _ _ (.cons_int _ _ _ (.int64 n) .nil)

example : decimal (-42) = go!"-42" := by simp [decimal, decimalNat_eq, digitByte]
example : decimalPad 5 (-42) = go!"-0042" := by
  simp [decimalPad, padZeros, decimalNat_eq, digitByte]
example : decimalPad 2 12345 = go!"12345" := by
  simp [decimalPad, padZeros, decimalNat_eq, digitByte]

end prefix_lemmas

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.fmt :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.fmt :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.fmt get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.fmt }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  repeat (wp_apply wp_GlobalAlloc (V := GoInterface) _ go.error as _)
  wp_apply wp_GlobalAlloc (V := sync.Pool) ssFree sync.Pool.ty as _
  wp_apply wp_GlobalAlloc (V := GoSlice) space _ as _
  wp_apply wp_GlobalAlloc (V := sync.Pool) ppFree sync.Pool.ty as _
  wp_apply sync.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hsync⟩
  wp_apply io.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hio⟩
  wp_apply errors.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Herrors⟩
  repeat (first
    | (wp_apply errors.wp_New as %_ _)
    | (rw [recv_eq_func_mk BAnon BAnon]; wp_auto)
    | wp_auto)
  wp_apply wp_slice_literal (V := GoArray w16 2)
    [array.mk 2 [W16 9, W16 13], array.mk 2 [W16 32, W16 32], array.mk 2 [W16 133, W16 133], array.mk 2 [W16 160, W16 160], array.mk 2 [W16 5760, W16 5760], array.mk 2 [W16 8192, W16 8202], array.mk 2 [W16 8232, W16 8233], array.mk 2 [W16 8239, W16 8239], array.mk 2 [W16 8287, W16 8287], array.mk 2 [W16 12288, W16 12288]]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, Hcap⟩
  repeat (first
    | (wp_apply errors.wp_New as %_ _)
    | (rw [recv_eq_func_mk BAnon BAnon]; wp_auto)
    | wp_auto)
  iframe Hown
  is_pkg_init_finish

/-- `fmt.Errorf(format, args...)` returns a non-nil error whose `Error()` returns some string.
The model of `Errorf` (`Perennial/TrustedCode/fmt.lean`) does not format: it is
`errors.New(format)`, ignoring the arguments, so this follows from `errors.wp_New`. (The
statement does not give back `args_sl ↦* args`, which the model never reads.) The arguments must
be of predeclared basic types (`ArgsWf`): Go's `Errorf` calls the `Error()`/`String()` methods of
other arguments, which the model does not, so for them it could panic or have effects the model
lacks. -/
theorem wp_Errorf (format : GoString) (args_sl : GoSlice) (args : List GoAny)
    (Hargs : ArgsWf args) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦* args }}
      (App (App (Val (@! Errorf)) (Val #format)) (Val #args_sl))
    {{ (err : GoInterfaceOk), RET #(interface.ok err);
        □ ∀ Φ : val → IProp GF, ▷ (∀ str : GoString, Φ #str) -∗
          WP (App (Val #(methods err.ty go!"Error" err.v)) (Val #())) {{ Φ }} }} := by
  wp_start as _
  wp_apply errors.wp_New as %err ⟨-, #Herr⟩
  iapply HΦ
  imodintro
  iintro %Φ HΦ
  iapply Herr
  inext
  iapply HΦ

/-- The helper `fmt.arbitraryString` of the model of `Sprintf` returns some string. -/
theorem wp_arbitraryString :
    {{ (True : IProp GF) }}
      (App (Val arbitraryString) (Val #()))
    {{ (s : GoString), RET #s; True }} := by
  iintro %Φ - HΦ
  unfold arbitraryString
  wp_auto
  ihave IH : iprop(∃ str : GoString, "s" ∷ s_ptr ↦ str) $$ [s]
  · iexists _; iframe
  wp_for IH
  wp_apply wp_ArbitraryInt as %c -
  wp_if_destruct
  · wp_apply wp_ArbitraryInt as %b -
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w8) (t := go.byte) [W8 (uint.Z b)]
    wp_auto
    rw [show go.arrayLiteralSize
      [KeyedElement none (ElementExpression go.byte #(W8 (uint.Z b)))] = 1 from rfl]
    isplitl []
    · ipureintro; rfl
    iintro %sl_ptr ⟨Hsl, -⟩
    wp_apply wp_bytes_to_string $$ Hsl as -
    wp_for_post
    iframe
    iexists _
    iframe
  · have Hf : (!decide (c = W64 0)) = false := by
      revert Hif; cases (!decide (c = W64 0)) <;> simp
    rw [Hf]
    simp only [_root_.decide_true, ↓reduceIte]
    wp_auto
    iapply HΦ; itrivial

/-- The integer of sign `neg` and magnitude `mag`. -/
def signedValue (neg : Bool) (mag : w64) : Int := if neg then -uint.Z mag else uint.Z mag

theorem decimalPad_signedValue_false (w : Nat) (mag : w64) :
    decimalPad w (signedValue false mag) = padZeros w (decimalNat (uint.nat mag)) := by
  have h : (uint.Z mag).natAbs = uint.nat mag := by word
  simp only [decimalPad, signedValue, Bool.false_eq_true, ↓reduceIte, h]
  rw [ite_eq_right (by word)]

theorem decimalPad_signedValue_true (w : Nat) (mag : w64) (hmag : uint.Z mag ≠ 0) :
    decimalPad w (signedValue true mag) = W8 45 :: padZeros (w - 1) (decimalNat (uint.nat mag)) := by
  have h : (-uint.Z mag).natAbs = uint.nat mag := by word
  simp only [decimalPad, signedValue, ↓reduceIte, h]
  rw [ite_eq_left (by word)]

/-- The helper `fmt.formatInt` of the model of `Sprintf`: the decimal of the integer of sign `neg`
and magnitude `mag` (non-zero if `neg`), zero-padded to `width`. -/
theorem wp_formatInt (neg : Bool) (mag width : w64) (hneg : neg = true → uint.Z mag ≠ 0)
    (hw : 0 ≤ sint.Z width ∧ sint.Z width ≤ 1000000) :
    {{ (True : IProp GF) }}
      (App (App (App (Val formatInt) (Val #neg)) (Val #mag)) (Val #width))
    {{ RET #(decimalPad (sint.nat width) (signedValue neg mag)); True }} := by
  iintro %Φ - HΦ
  unfold formatInt
  wp_auto
  ihave IH : iprop(∃ (m : w64) (ds : GoString),
      "mag" ∷ mag_ptr ↦ m ∗
      "digits" ∷ digits_ptr ↦ ds ∗
      "%Hds" ∷ ⌜decimalNat (uint.nat mag) = decimalNat (uint.nat m) ++ ds⌝) $$ [mag digits]
  · iexists _, _
    iframe
    ipureintro
    simp [show zero_val GoString = [] from rfl]
  wp_for IH
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 (uint.Z (m % W64 10)) + W8 48]
  wp_auto
  rw [show go.arrayLiteralSize
    [KeyedElement none (ElementExpression go.byte #(W8 (uint.Z (m % W64 10)) + W8 48))] = 1 from rfl]
  isplitl []
  · ipureintro; rfl
  iintro %sl_ptr ⟨Hsl, -⟩
  wp_apply wp_bytes_to_string $$ Hsl as -
  have Hdig : W8 (uint.Z (m % W64 10)) + W8 48 = digitByte (uint.nat m % 10) := by
    unfold digitByte; word
  rw [Hdig]
  wp_if_destruct
  · -- the last digit
    wp_for_post
    have Hm : uint.nat m < 10 := by
      have := congrArg uint.Z Hif; word
    have HD : decimalNat (uint.nat mag) = [digitByte (uint.nat m % 10)] ++ ds := by
      rw [Hds, decimalNat_of_lt Hm, Nat.mod_eq_of_lt Hm]
    rw [← HD]
    generalize HDdef : decimalNat (uint.nat mag) = D
    have HDlen : D.length ≤ 20 := by
      rw [← HDdef]
      exact length_decimalNat_le _ 20 (by omega) (by word)
    -- the width without the sign
    obtain ⟨w1, W, Hw1, HW, Hwc⟩ : ∃ (w1 : w64) (W : Nat),
        (if neg then width - W64 1 else width) = w1 ∧
        W = (if neg then sint.nat width - 1 else sint.nat width) ∧
        ∀ n : Nat, n < 2 ^ 63 → (sint.Z (W64 n) < sint.Z w1 ↔ n < W) := by
      refine ⟨_, _, rfl, rfl, ?_⟩
      intro n hn
      cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> (try word)
    cases neg
    all_goals
      simp only [Bool.false_eq_true, ↓reduceIte] at Hw1 HW
      subst Hw1
      wp_auto
      ihave IH2 : iprop(∃ (k : Nat),
          "digits" ∷ digits_ptr ↦ (List.replicate k (W8 48) ++ D) ∗
          "%Hk" ∷ ⌜k ≤ W - D.length⌝) $$ [digits]
      · iexists 0; iframe; ipureintro; simp
      wp_for IH2
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hlen
      wp_if_destruct
      · -- one more `0`
        have Hlt := (Hwc _ Hlen).1 (of_decide_eq_true (go.intoVal_inj Hif))
        wp_for_post
        iframe
        iexists k + 1
        have h48 : (48#8 : w8) = W8 48 := by decide
        rw [h48, List.singleton_append,
          show W8 48 :: (List.replicate k (W8 48) ++ D) = List.replicate (k + 1) (W8 48) ++ D from rfl]
        iframe
        ipureintro
        simp only [List.length_append, List.length_replicate] at Hlt
        omega
      · have Hge : ¬ (List.replicate k (W8 48) ++ D).length < W := fun h =>
          Hif (by rw [decide_eq_true ((Hwc _ Hlen).2 h)])
        simp only [decide_eq_false (fun h => Hge ((Hwc _ Hlen).1 h)),
          Bool.false_eq_true, ↓reduceIte]
        have Hpad : List.replicate k (W8 48) ++ D = padZeros W D := by
          unfold padZeros
          simp only [List.length_append, List.length_replicate] at Hge
          congr 2
          omega
        rw [Hpad]
        wp_auto
        rw [← HDdef]
        first
        | rw [decimalPad_signedValue_false, ← HW]
        | rw [decimalPad_signedValue_true _ _ (hneg rfl), ← HW,
            show ([45#8] ++ padZeros W (decimalNat (uint.nat mag))) =
              W8 45 :: padZeros W (decimalNat (uint.nat mag)) from by
                rw [show (45#8 : w8) = W8 45 by decide]; rfl]
        iapply HΦ
        itrivial
    done
  · wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro
    have Hm : 10 ≤ uint.nat m := by
      have : m / W64 10 ≠ W64 0 := fun h => Hif (by rw [h])
      word
    rw [Hds, decimalNat_of_ge Hm, show uint.nat (m / W64 10) = uint.nat m / 10 by word]
    simp

/-- The helper `fmt.intVerb` of the model of `Sprintf`: at the `%` at index `i` of `format`, the
integer directive that follows, `parseIntVerb` of the format after the `%`, with the index after
it. -/
theorem wp_intVerb (format : GoString) (i : w64)
    (Hi : 0 ≤ sint.Z i ∧ sint.Z i < (format.length : Int)) :
    {{ (True : IProp GF) }}
      (App (App (Val intVerb) (Val #format)) (Val #i))
    {{ (w next : w64) (ok : Bool), RET (PairV (PairV #w #next) #ok);
        ⌜ok = true → parseIntVerb (format.drop (sint.nat i + 1)) =
            some (sint.nat w, format.drop (sint.nat next)) ∧
          0 ≤ sint.Z w ∧ sint.Z w ≤ 1000000 ∧ sint.Z i < sint.Z next ∧
          sint.Z next ≤ (format.length : Int)⌝ ∗
        ⌜ok = false → parseIntVerb (format.drop (sint.nat i + 1)) = none⌝ }} := by
  iintro %Φ - HΦ
  unfold intVerb
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hflen
  wp_if_destruct
  · -- a byte `c` after the `%`
    have Hlt : sint.nat i + 1 < format.length := by word
    obtain ⟨c, Hc, Hdrop⟩ : ∃ c, format[sint.nat i + 1]? = some c ∧
        format.drop (sint.nat i + 1) = c :: format.drop (sint.nat i + 2) :=
      ⟨_, List.getElem?_eq_getElem Hlt, List.drop_eq_getElem_cons Hlt⟩
    have Hidx : format[sint.nat (i + W64 1)]? = some c := by
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]; exact Hc
    rw [Hidx]
    wp_auto
    have Hdrop2 : sint.nat (i + W64 2) = sint.nat i + 2 := by word
    by_cases hd : c = W8 100 ∨ c = W8 118
    · -- `%d` or `%v`
      rcases hd with h | h
      · subst h
        simp only [_root_.decide_true]
        wp_auto
        iapply HΦ
        isplitl []
        · ipureintro; intro _
          rw [Hdrop, Hdrop2]
          refine ⟨by simp [parseIntVerb] <;> rfl, by word, by word, by word, by word⟩
        · ipureintro; intro h; cases h
      · subst h
        rw [decide_eq_false (by decide)]
        wp_auto
        rw [Hidx]
        wp_auto
        iapply HΦ
        isplitl []
        · ipureintro; intro _
          rw [Hdrop, Hdrop2]
          refine ⟨by simp [parseIntVerb] <;> rfl, by word, by word, by word, by word⟩
        · ipureintro; intro h; cases h
    · rw [not_or] at hd
      rw [decide_eq_false hd.1]
      wp_auto
      rw [Hidx]
      wp_auto
      rw [decide_eq_false hd.2]
      wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
      rw [decide_eq_true Hif]
      wp_auto
      rw [Hidx]
      wp_auto
      by_cases h0 : c = W8 48
      · subst h0
        simp only [_root_.decide_true]
        wp_auto
        ihave IH : iprop(∃ (jv wv : w64) (Wn : Nat),
            "j" ∷ j_ptr ↦ jv ∗
            "width" ∷ width_ptr ↦ wv ∗
            "%Hinv" ∷ ⌜sint.Z wv = Wn ∧ Wn ≤ 10000009 ∧ sint.Z i + 2 ≤ sint.Z jv ∧
              sint.Z jv ≤ format.length ∧
              scanWidth 0 (format.drop (sint.nat i + 2)) =
                scanWidth Wn (format.drop (sint.nat jv))⌝) $$ [j width]
        · iexists _, _, 0
          iframe
          ipureintro
          refine ⟨rfl, by omega, by word, by word, by rw [Hdrop2]⟩
        wp_for IH
        obtain ⟨HWn, HWb, Hj1, Hj2, Hscan⟩ := Hinv
        wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
        wp_if_destruct
        rotate_left
        have Hexit : scanWidth Wn (format.drop (sint.nat jv)) =
            (Wn, format.drop (sint.nat jv)) := by
          rw [List.drop_eq_nil_of_le (by word)]; rfl
        rotate_right
        have Hjlt : sint.nat jv < format.length := by word
        obtain ⟨cj, Hcj, Hdropj⟩ : ∃ cj, format[sint.nat jv]? = some cj ∧
            format.drop (sint.nat jv) = cj :: format.drop (sint.nat jv + 1) :=
          ⟨_, List.getElem?_eq_getElem Hjlt, List.drop_eq_getElem_cons Hjlt⟩
        rw [Hcj]
        wp_auto
        wp_if_destruct
        rotate_left
        have Hexit : scanWidth Wn (format.drop (sint.nat jv)) =
            (Wn, format.drop (sint.nat jv)) := by
          rw [Hdropj, scanWidth, ite_eq_right (by rintro ⟨h1, -, -⟩; apply Hif; word)]
        rotate_right
        rw [Hcj]
        wp_auto
        wp_if_destruct
        rotate_left
        have Hexit : scanWidth Wn (format.drop (sint.nat jv)) =
            (Wn, format.drop (sint.nat jv)) := by
          rw [Hdropj, scanWidth, ite_eq_right (by rintro ⟨-, h2, -⟩; apply Hif; word)]
        rotate_right
        by_cases Hwle : sint.Z wv ≤ sint.Z (W64 1000000)
        rotate_left
        have Hexit : scanWidth Wn (format.drop (sint.nat jv)) =
            (Wn, format.drop (sint.nat jv)) := by
          rw [Hdropj, scanWidth, ite_eq_right (by rintro ⟨-, -, h3⟩; apply Hwle; word)]
        simp only [decide_eq_false Hwle, Bool.false_eq_true, ↓reduceIte]
        rotate_right
        simp only [decide_eq_true Hwle, ↓reduceIte]
        -- a digit: the loop goes on
        wp_auto
        rw [Hcj]
        wp_auto
        wp_for_post
        iframe
        iexists _, _, Wn * 10 + (uint.nat cj - 48)
        iframe
        ipureintro
        refine ⟨by word, by word, by word, by word, ?_⟩
        rw [Hscan, Hdropj, scanWidth, ite_eq_left ⟨by word, by word, by word⟩,
          show sint.nat (jv + W64 1) = sint.nat jv + 1 by word]
        -- the end of the width: the four ways out of the loop
        all_goals
          have Hsc : scanWidth 0 (format.drop (sint.nat i + 2)) =
              (Wn, format.drop (sint.nat jv)) := Hscan.trans Hexit
          have Hparse : parseIntVerb (format.drop (sint.nat i + 1)) =
              (match format.drop (sint.nat jv) with
                | d :: rest =>
                  if (d :: rest).length < (format.drop (sint.nat i + 2)).length ∧ d = W8 100 ∧
                    Wn ≤ 1000000 then some (Wn, rest) else none
                | [] => none) := by
            rw [Hdrop, parseIntVerb, ite_eq_right (by rintro (h | h) <;> simp_all),
              ite_eq_left rfl, Hsc]
            generalize format.drop (sint.nat jv) = l
            cases l <;> rfl
          clear Hexit Hscan Hsc
          (try wp_auto)
          wp_if_destruct
          · -- a digit was read
            wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
            wp_if_destruct
            · have Hk : sint.nat jv < format.length := by word
              obtain ⟨ck, Hck, Hdropk⟩ : ∃ ck, format[sint.nat jv]? = some ck ∧
                  format.drop (sint.nat jv) = ck :: format.drop (sint.nat jv + 1) :=
                ⟨_, List.getElem?_eq_getElem Hk, List.drop_eq_getElem_cons Hk⟩
              rw [Hck]
              wp_auto
              by_cases hck : ck = W8 100
              · subst hck
                simp only [_root_.decide_true]
                wp_auto
                by_cases Hwle' : sint.Z wv ≤ sint.Z (W64 1000000)
                · simp only [decide_eq_true Hwle']
                  wp_auto
                  iapply HΦ
                  isplitl []
                  · ipureintro; intro _
                    refine ⟨?_, by word, by word, by word, by word⟩
                    rw [Hparse, Hdropk]
                    dsimp only
                    rw [ite_eq_left ⟨by simp; word, rfl, by word⟩,
                      show sint.nat (jv + W64 1) = sint.nat jv + 1 by word,
                      show sint.nat wv = Wn by word]
                  · ipureintro; intro h; cases h
                · simp only [decide_eq_false Hwle']
                  wp_auto
                  iapply HΦ
                  isplitl []
                  · ipureintro; intro h; cases h
                  · ipureintro; intro _
                    rw [Hparse, Hdropk]
                    dsimp only
                    rw [ite_eq_right (by rintro ⟨-, -, h⟩; apply Hwle'; word)]
              · rw [decide_eq_false hck]
                wp_auto
                iapply HΦ
                isplitl []
                · ipureintro; intro h; cases h
                · ipureintro; intro _
                  rw [Hparse, Hdropk]
                  dsimp only
                  rw [ite_eq_right (by rintro ⟨-, h, -⟩; exact hck h)]
            · iapply HΦ
              isplitl []
              · ipureintro; intro h; cases h
              · ipureintro; intro _
                rw [Hparse, List.drop_eq_nil_of_le (by word)]
          · -- no digit
            iapply HΦ
            isplitl []
            · ipureintro; intro h; cases h
            · ipureintro; intro _
              rw [Hparse, show sint.nat jv = sint.nat i + 2 by word]
              split
              · rw [ite_eq_right (by rintro ⟨h, -, -⟩; simp_all)]
              · rfl
      · rw [decide_eq_false h0]
        wp_auto
        iapply HΦ
        isplitl []
        · ipureintro; intro h; cases h
        · ipureintro; intro _
          rw [Hdrop]
          simp only [parseIntVerb, hd.1, hd.2, h0, _root_.or_self, ↓reduceIte]
  · -- a trailing `%`
    have Hnil : format.drop (sint.nat i + 1) = [] := List.drop_eq_nil_of_le (by word)
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
    wp_if_destruct
    · exfalso; word
    · iapply HΦ
      isplitl []
      · ipureintro; intro h; cases h
      · ipureintro; intro _; rw [Hnil]; rfl

set_option maxRecDepth 100000 in
/-- The helper `fmt.intArg` of the model of `Sprintf`: the sign and magnitude of the integer an
argument holds, if its dynamic type is one of Go's integer types. -/
theorem wp_intArg (x : GoInterface) (Hx : ∀ ii, x = interface.ok ii → ArgWf ii) :
    {{ (True : IProp GF) }}
      (App (Val intArg) (Val #x))
    {{ (neg : Bool) (mag : w64) (ok : Bool), RET (PairV (PairV #neg #mag) #ok);
        ⌜ok = true → ∃ ii, x = interface.ok ii ∧ IntArgValue ii (signedValue neg mag) ∧
          (neg = true → uint.Z mag ≠ 0)⌝ ∗
        ⌜ok = false → ∀ ii, x = interface.ok ii → ¬ IsIntType ii.ty⌝ }} := by
  iintro %Φ - HΦ
  unfold intArg
  wp_auto
  cases x with
  | nil =>
    wp_auto
    iapply HΦ
    isplitl []
    · ipureintro; simp
    · ipureintro; intro _ ii h; cases h
  | ok ii =>
    obtain ⟨ty, v⟩ := ii
    wp_auto
    by_cases h1 : ty = go.int
    · subst h1
      obtain ⟨z, hz⟩ := (Hx _ rfl).2.1 (by simp [IsIntType])
      obtain ⟨n, rfl, rfl⟩ := IntArgValue.of_int hz
      simp only [↓reduceIte, _root_.decide_true]
      wp_auto
      wp_if_destruct
      · iapply HΦ
        isplitl []
        · ipureintro; intro _
          exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [↓reduceIte] <;> word), fun _ => by word⟩
        · ipureintro; intro h; cases h
      · iapply HΦ
        isplitl []
        · ipureintro; intro _
          exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [Bool.false_eq_true, ↓reduceIte] <;> word),
            fun h => by cases h⟩
        · ipureintro; intro h; cases h
    simp only [h1, ↓reduceIte, decide_false]
    wp_auto
    by_cases h2 : ty = go.int64
    · subst h2
      obtain ⟨z, hz⟩ := (Hx _ rfl).2.1 (by simp [IsIntType])
      obtain ⟨n, rfl, rfl⟩ := IntArgValue.of_int64 hz
      simp only [↓reduceIte, _root_.decide_true]
      wp_auto
      wp_if_destruct
      · iapply HΦ
        isplitl []
        · ipureintro; intro _
          exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [↓reduceIte] <;> word), fun _ => by word⟩
        · ipureintro; intro h; cases h
      · iapply HΦ
        isplitl []
        · ipureintro; intro _
          exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [Bool.false_eq_true, ↓reduceIte] <;> word),
            fun h => by cases h⟩
        · ipureintro; intro h; cases h
    simp only [h2, ↓reduceIte, decide_false]
    wp_auto
    by_cases h3 : ty = go.int32
    · subst h3
      obtain ⟨z, hz⟩ := (Hx _ rfl).2.1 (by simp [IsIntType])
      obtain ⟨n, rfl, rfl⟩ := IntArgValue.of_int32 hz
      simp only [↓reduceIte, _root_.decide_true]
      wp_auto
      wp_if_destruct
      · iapply HΦ
        isplitl []
        · ipureintro; intro _
          exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [↓reduceIte] <;> word), fun _ => by word⟩
        · ipureintro; intro h; cases h
      · iapply HΦ
        isplitl []
        · ipureintro; intro _
          exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [Bool.false_eq_true, ↓reduceIte] <;> word),
            fun h => by cases h⟩
        · ipureintro; intro h; cases h
    simp only [h3, ↓reduceIte, decide_false]
    wp_auto
    by_cases h4 : ty = go.int16
    · subst h4
      obtain ⟨z, hz⟩ := (Hx _ rfl).2.1 (by simp [IsIntType])
      obtain ⟨n, rfl, rfl⟩ := IntArgValue.of_int16 hz
      simp only [↓reduceIte, _root_.decide_true]
      wp_auto
      wp_if_destruct
      · iapply HΦ
        isplitl []
        · ipureintro; intro _
          exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [↓reduceIte] <;> word), fun _ => by word⟩
        · ipureintro; intro h; cases h
      · iapply HΦ
        isplitl []
        · ipureintro; intro _
          exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [Bool.false_eq_true, ↓reduceIte] <;> word),
            fun h => by cases h⟩
        · ipureintro; intro h; cases h
    simp only [h4, ↓reduceIte, decide_false]
    wp_auto
    by_cases h5 : ty = go.int8
    · subst h5
      obtain ⟨z, hz⟩ := (Hx _ rfl).2.1 (by simp [IsIntType])
      obtain ⟨n, rfl, rfl⟩ := IntArgValue.of_int8 hz
      simp only [↓reduceIte, _root_.decide_true]
      wp_auto
      wp_if_destruct
      · iapply HΦ
        isplitl []
        · ipureintro; intro _
          exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [↓reduceIte] <;> word), fun _ => by word⟩
        · ipureintro; intro h; cases h
      · iapply HΦ
        isplitl []
        · ipureintro; intro _
          exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [Bool.false_eq_true, ↓reduceIte] <;> word),
            fun h => by cases h⟩
        · ipureintro; intro h; cases h
    simp only [h5, ↓reduceIte, decide_false]
    wp_auto
    by_cases h6 : ty = go.uint
    · subst h6
      obtain ⟨z, hz⟩ := (Hx _ rfl).2.1 (by simp [IsIntType])
      obtain ⟨n, rfl, rfl⟩ := IntArgValue.of_uint hz
      simp only [↓reduceIte, _root_.decide_true]
      wp_auto
      iapply HΦ
      isplitl []
      · ipureintro; intro _
        exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [Bool.false_eq_true, ↓reduceIte] <;> word),
          fun h => by cases h⟩
      · ipureintro; intro h; cases h
    simp only [h6, ↓reduceIte, decide_false]
    wp_auto
    by_cases h7 : ty = go.uint64
    · subst h7
      obtain ⟨z, hz⟩ := (Hx _ rfl).2.1 (by simp [IsIntType])
      obtain ⟨n, rfl, rfl⟩ := IntArgValue.of_uint64 hz
      simp only [↓reduceIte, _root_.decide_true]
      wp_auto
      iapply HΦ
      isplitl []
      · ipureintro; intro _
        exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [Bool.false_eq_true, ↓reduceIte] <;> word),
          fun h => by cases h⟩
      · ipureintro; intro h; cases h
    simp only [h7, ↓reduceIte, decide_false]
    wp_auto
    by_cases h8 : ty = go.uint32
    · subst h8
      obtain ⟨z, hz⟩ := (Hx _ rfl).2.1 (by simp [IsIntType])
      obtain ⟨n, rfl, rfl⟩ := IntArgValue.of_uint32 hz
      simp only [↓reduceIte, _root_.decide_true]
      wp_auto
      iapply HΦ
      isplitl []
      · ipureintro; intro _
        exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [Bool.false_eq_true, ↓reduceIte] <;> word),
          fun h => by cases h⟩
      · ipureintro; intro h; cases h
    simp only [h8, ↓reduceIte, decide_false]
    wp_auto
    by_cases h9 : ty = go.uint16
    · subst h9
      obtain ⟨z, hz⟩ := (Hx _ rfl).2.1 (by simp [IsIntType])
      obtain ⟨n, rfl, rfl⟩ := IntArgValue.of_uint16 hz
      simp only [↓reduceIte, _root_.decide_true]
      wp_auto
      iapply HΦ
      isplitl []
      · ipureintro; intro _
        exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [Bool.false_eq_true, ↓reduceIte] <;> word),
          fun h => by cases h⟩
      · ipureintro; intro h; cases h
    simp only [h9, ↓reduceIte, decide_false]
    wp_auto
    by_cases h10 : ty = go.uint8
    · subst h10
      obtain ⟨z, hz⟩ := (Hx _ rfl).2.1 (by simp [IsIntType])
      obtain ⟨n, rfl, rfl⟩ := IntArgValue.of_uint8 hz
      simp only [↓reduceIte, _root_.decide_true]
      wp_auto
      iapply HΦ
      isplitl []
      · ipureintro; intro _
        exact ⟨_, rfl, hz.cast (by unfold signedValue; simp only [Bool.false_eq_true, ↓reduceIte] <;> word),
          fun h => by cases h⟩
      · ipureintro; intro h; cases h
    simp only [h10, ↓reduceIte, decide_false]
    wp_auto
    iapply HΦ
    isplitl []
    · ipureintro; intro h; cases h
    · ipureintro
      intro _ ii h
      cases h
      simp only [IsIntType, not_or]
      exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

omit [FfiSemantics ext ffi] in
theorem not_simpleDirective (f : GoString) (x : GoInterface) (args : List GoInterface)
    (h1 : f.head? ≠ some (W8 37))
    (h2 : f.head? ≠ some (W8 115) ∨ ∀ ii, x = interface.ok ii → ii.ty ≠ go.string)
    (h3 : parseIntVerb f = none ∨ ∀ ii, x = interface.ok ii → ¬ IsIntType ii.ty) :
    ¬ SimpleDirective f (x :: args) := by
  cases f with
  | nil => simp [SimpleDirective]
  | cons c f =>
    simp only [SimpleDirective, List.cons.injEq]
    rintro (h | ⟨hc, ii, rest, ⟨rfl, -⟩, hty⟩ | ⟨hp, ii, rest, ⟨rfl, -⟩, hty⟩)
    · exact h1 (by simp [h])
    · rcases h2 with h2 | h2
      · exact h2 (by simp [hc])
      · exact h2 ii rfl hty
    · rcases h3 with h3 | h3
      · rw [h3] at hp; simp at hp
      · exact h3 ii rfl hty

omit [FfiSemantics ext ffi] in
theorem not_simpleDirective_nil (f : GoString) (h : f.head? ≠ some (W8 37)) :
    ¬ SimpleDirective f [] := by
  cases f with
  | nil => simp [SimpleDirective]
  | cons c f =>
    simp only [SimpleDirective]
    rintro (h' | ⟨-, ii, rest, h', -⟩ | ⟨-, ii, rest, h', -⟩)
    · exact h (by simp [h'])
    · cases h'
    · cases h'

/-- The helper `fmt.formatArg` of the model of `Sprintf`: at the `%` at index `i` of `format`, the
output of the directive for the argument `x` and the index after it, if the model formats it. -/
theorem wp_formatArg (format : GoString) (i : w64) (x : GoInterface)
    (Hi : 0 ≤ sint.Z i ∧ sint.Z i < (format.length : Int))
    (Hx : ∀ ii, x = interface.ok ii → ArgWf ii) :
    {{ (True : IProp GF) }}
      (App (App (App (Val formatArg) (Val #format)) (Val #i)) (Val #x))
    {{ (s : GoString) (next : w64) (ok : Bool), RET (PairV (PairV #s #next) #ok);
        ⌜ok = true → sint.Z i < sint.Z next ∧ sint.Z next ≤ (format.length : Int) ∧
          ∀ args r, SprintfOut (format.drop (sint.nat next)) args r →
            SprintfOut (W8 37 :: format.drop (sint.nat i + 1)) (x :: args) (s ++ r)⌝ ∗
        ⌜ok = false → (format.drop (sint.nat i + 1)).head? ≠ some (W8 37) →
          ∀ args, ¬ SimpleDirective (format.drop (sint.nat i + 1)) (x :: args)⌝ }} := by
  iintro %Φ - HΦ
  unfold formatArg
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hflen
  wp_if_destruct
  · have Hlt : sint.nat i + 1 < format.length := by word
    have Hdrop2 : sint.nat (i + W64 2) = sint.nat i + 2 := by word
    obtain ⟨c, Hc, Hdrop⟩ : ∃ c, format[sint.nat i + 1]? = some c ∧
        format.drop (sint.nat i + 1) = c :: format.drop (sint.nat i + 2) :=
      ⟨_, List.getElem?_eq_getElem Hlt, List.drop_eq_getElem_cons Hlt⟩
    have Hidx : format[sint.nat (i + W64 1)]? = some c := by
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]; exact Hc
    rw [Hidx]
    wp_auto
    by_cases hs : c = W8 115
    · -- `%s`
      subst hs
      simp only [_root_.decide_true]
      have Hnp : parseIntVerb (format.drop (sint.nat i + 1)) = none := by
        rw [Hdrop]; simp [parseIntVerb]
      cases x with
      | nil =>
        wp_auto
        iapply HΦ
        isplitl []
        · ipureintro; intro h; cases h
        · ipureintro; intro _ hp args
          exact not_simpleDirective _ _ _ hp (.inr (fun ii h => by cases h)) (.inl Hnp)
      | ok ii =>
        by_cases hty : ii.ty = go.string
        · obtain ⟨sx, hv⟩ := (Hx ii rfl).1 hty
          obtain ⟨ty, v⟩ := ii
          simp only at hty hv
          subst hty hv
          wp_auto
          iapply HΦ
          isplitl []
          · ipureintro; intro _
            refine ⟨by word, by word, fun args r hr => ?_⟩
            rw [Hdrop2] at hr
            rw [Hdrop]
            exact SprintfOut.str sx _ _ _ hr
          · ipureintro; intro h; cases h
        · wp_auto
          simp only [hty, ↓reduceIte, decide_false]
          wp_auto
          iapply HΦ
          isplitl []
          · ipureintro; intro h; cases h
          · ipureintro; intro _ hp args
            exact not_simpleDirective _ _ _ hp
              (.inr (fun ii' h => by cases h; exact hty)) (.inl Hnp)
    · rw [decide_eq_false hs]
      wp_auto
      have Hns : (format.drop (sint.nat i + 1)).head? ≠ some (W8 115) := by
        rw [Hdrop]; simpa using hs
      wp_apply wp_intVerb format i Hi as %w %next %ok ⟨%Hv1, %Hv2⟩
      cases ok
      · wp_auto
        iapply HΦ
        isplitl []
        · ipureintro; intro h; cases h
        · ipureintro; intro _ hp args
          exact not_simpleDirective _ _ _ hp (.inl Hns) (.inl (Hv2 rfl))
      · obtain ⟨Hparse, Hw1, Hw2, Hn1, Hn2⟩ := Hv1 rfl
        wp_auto
        wp_apply wp_intArg x Hx as %neg %mag %ok2 ⟨%Ha1, %Ha2⟩
        cases ok2
        · wp_auto
          iapply HΦ
          isplitl []
          · ipureintro; intro h; cases h
          · ipureintro; intro _ hp args
            exact not_simpleDirective _ _ _ hp (.inl Hns) (.inr (Ha2 rfl))
        · obtain ⟨ii, rfl, Hval, Hmag⟩ := Ha1 rfl
          wp_auto
          wp_apply wp_formatInt neg mag w Hmag ⟨Hw1, Hw2⟩
          iapply HΦ
          isplitl []
          · ipureintro; intro _
            exact ⟨Hn1, Hn2, fun args r hr => SprintfOut.int _ _ _ _ _ _ _ Hparse Hval hr⟩
          · ipureintro; intro h; cases h
  · (try wp_auto)
    have Hns : (format.drop (sint.nat i + 1)).head? ≠ some (W8 115) := by
      rw [List.drop_eq_nil_of_le (by word)]; simp
    wp_apply wp_intVerb format i Hi as %w %next %ok ⟨%Hv1, %Hv2⟩
    cases ok
    · wp_auto
      iapply HΦ
      isplitl []
      · ipureintro; intro h; cases h
      · ipureintro; intro _ hp args
        exact not_simpleDirective _ _ _ hp (.inl Hns) (.inl (Hv2 rfl))
    · obtain ⟨Hparse, Hw1, Hw2, Hn1, Hn2⟩ := Hv1 rfl
      wp_auto
      wp_apply wp_intArg x Hx as %neg %mag %ok2 ⟨%Ha1, %Ha2⟩
      cases ok2
      · wp_auto
        iapply HΦ
        isplitl []
        · ipureintro; intro h; cases h
        · ipureintro; intro _ hp args
          exact not_simpleDirective _ _ _ hp (.inl Hns) (.inr (Ha2 rfl))
      · obtain ⟨ii, rfl, Hval, Hmag⟩ := Ha1 rfl
        wp_auto
        wp_apply wp_formatInt neg mag w Hmag ⟨Hw1, Hw2⟩
        iapply HΦ
        isplitl []
        · ipureintro; intro _
          exact ⟨Hn1, Hn2, fun args r hr => SprintfOut.int _ _ _ _ _ _ _ Hparse Hval hr⟩
        · ipureintro; intro h; cases h

/-- `fmt.Sprintf(format, args...)` returns a string `s` with `SprintfOut format args s`: `%%`,
`%s` of a `string`, and `%d`, `%v` and `%0Nd` of an integer are formatted, the rest of the output
is arbitrary from any other directive on (see the model of `Sprintf`,
`Perennial/TrustedCode/fmt.lean`). The arguments' values must be of their dynamic types where
these are `string` or an integer type (`ArgsWf`). -/
theorem wp_Sprintf (format : GoString) (args_sl : GoSlice) (xs : List GoInterface) (dq : DFrac)
    (Hxs : ArgsWf xs) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs }}
      (App (App (Val (@! Sprintf)) (Val #format)) (Val #args_sl))
    {{ (s : GoString), RET #s; args_sl ↦*{dq} xs ∗ ⌜SprintfOut format xs s⌝ }} := by
  wp_start as Hsl
  wp_auto
  ihave %Hxlen := ownSlice_len $$ Hsl
  ihave IH : iprop(∃ (n k : w64) (acc : GoString),
      "i" ∷ i_ptr ↦ n ∗
      "argNum" ∷ argNum_ptr ↦ k ∗
      "out" ∷ out_ptr ↦ acc ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (format.length : Int)⌝ ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (xs.length : Int)⌝ ∗
      "%Hacc" ∷ ⌜∀ r, SprintfOut (format.drop (sint.nat n)) (xs.drop (sint.nat k)) r →
        SprintfOut format xs (acc ++ r)⌝) $$ [i argNum out]
  · iexists _, _, _
    iframe
    ipureintro
    rw [show zero_val w64 = W64 0 from rfl, show zero_val GoString = [] from rfl,
      show sint.nat (W64 0) = 0 from rfl]
    exact ⟨⟨by word, by word⟩, ⟨by word, by word⟩, fun r h => by simpa using h⟩
  wp_for IH
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hflen
  wp_if_destruct
  · have Hif' := of_decide_eq_true (go.intoVal_inj Hif)
    have Hlt : sint.nat n < format.length := by word
    obtain ⟨c, Hc, Hdrop⟩ : ∃ c, format[sint.nat n]? = some c ∧
        format.drop (sint.nat n) = c :: format.drop (sint.nat n + 1) :=
      ⟨_, List.getElem?_eq_getElem Hlt, List.drop_eq_getElem_cons Hlt⟩
    rw [Hc]
    wp_auto
    wp_if_destruct
    · -- `%`
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
      wp_if_destruct
      · -- `%` and a byte `d` after it
        have Hlt1 : sint.nat n + 1 < format.length := by word
        obtain ⟨d, Hd, Hdrop1⟩ : ∃ d, format[sint.nat n + 1]? = some d ∧
            format.drop (sint.nat n + 1) = d :: format.drop (sint.nat n + 2) :=
          ⟨_, List.getElem?_eq_getElem Hlt1, List.drop_eq_getElem_cons Hlt1⟩
        rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, Hd]
        wp_auto
        wp_if_destruct
        · -- `%%`
          wp_for_post
          iframe
          iexists _, _, _
          iframe
          ipureintro
          refine ⟨⟨by word, by word⟩, ⟨by word, by word⟩, fun r h => ?_⟩
          rw [show sint.nat (n + W64 2) = sint.nat n + 2 by word] at h
          have := Hacc (W8 37 :: r) (by rw [Hdrop, Hdrop1]; exact .percent _ _ _ h)
          simpa using this
        · -- `%` and a byte `d` other than `%`
          have Hnp : (format.drop (sint.nat n + 1)).head? ≠ some (W8 37) := by
            rw [Hdrop1]; simpa using Hif
          wp_if_destruct
          · -- an argument is left
            simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z args_sl.len from ⟨Hk.1, Hif⟩,
              and_self, ↓reduceIte]
            have Hklt : sint.nat k < xs.length := by word
            obtain ⟨x, Hx, Hdropk⟩ : ∃ x, xs[sint.nat k]? = some x ∧
                xs.drop (sint.nat k) = x :: xs.drop (sint.nat k + 1) :=
              ⟨_, List.getElem?_eq_getElem Hklt, List.drop_eq_getElem_cons Hklt⟩
            wp_apply wp_load_slice_index args_sl (sint.Z k) xs dq x Hk.1 $$ [Hsl] with Hsl
            · iframe; ipureintro; exact Hx
            have Hxmem : x ∈ xs := List.mem_of_getElem? Hx
            wp_apply wp_formatArg format n x ⟨Hn.1, by word⟩
              (fun ii h => Hxs ii (h ▸ Hxmem)) as %s %next %ok ⟨%Hf1, %Hf2⟩
            cases ok
            · wp_auto
              wp_apply wp_arbitraryString as %junk -
              wp_for_post
              iapply HΦ
              iframe
              ipureintro
              refine Hacc junk ?_
              rw [Hdrop, Hdropk]
              exact .other _ _ _ (Hf2 rfl Hnp _)
            · obtain ⟨Hn1, Hn2, Hout⟩ := Hf1 rfl
              wp_auto
              wp_for_post
              iframe
              iexists _, _, _
              iframe
              ipureintro
              refine ⟨⟨by word, by word⟩, ⟨by word, by word⟩, fun r h => ?_⟩
              rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word] at h
              have := Hacc (s ++ r) (by rw [Hdrop, Hdropk]; exact Hout _ _ h)
              simpa using this
          · -- no argument left
            wp_apply wp_arbitraryString as %junk -
            wp_for_post
            iapply HΦ
            iframe
            ipureintro
            refine Hacc junk ?_
            rw [Hdrop, show xs.drop (sint.nat k) = [] from List.drop_eq_nil_of_le (by word)]
            exact .other _ _ _ (not_simpleDirective_nil _ Hnp)
      · -- a trailing `%`
        have Hnp : (format.drop (sint.nat n + 1)).head? ≠ some (W8 37) := by
          rw [List.drop_eq_nil_of_le (by word)]; simp
        (try wp_auto)
        wp_if_destruct
        · -- an argument is left
          simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z args_sl.len from ⟨Hk.1, Hif⟩,
            and_self, ↓reduceIte]
          have Hklt : sint.nat k < xs.length := by word
          obtain ⟨x, Hx, Hdropk⟩ : ∃ x, xs[sint.nat k]? = some x ∧
              xs.drop (sint.nat k) = x :: xs.drop (sint.nat k + 1) :=
            ⟨_, List.getElem?_eq_getElem Hklt, List.drop_eq_getElem_cons Hklt⟩
          wp_apply wp_load_slice_index args_sl (sint.Z k) xs dq x Hk.1 $$ [Hsl] with Hsl
          · iframe; ipureintro; exact Hx
          have Hxmem : x ∈ xs := List.mem_of_getElem? Hx
          wp_apply wp_formatArg format n x ⟨Hn.1, by word⟩
            (fun ii h => Hxs ii (h ▸ Hxmem)) as %s %next %ok ⟨%Hf1, %Hf2⟩
          cases ok
          · wp_auto
            wp_apply wp_arbitraryString as %junk -
            wp_for_post
            iapply HΦ
            iframe
            ipureintro
            refine Hacc junk ?_
            rw [Hdrop, Hdropk]
            exact .other _ _ _ (Hf2 rfl Hnp _)
          · obtain ⟨Hn1, Hn2, Hout⟩ := Hf1 rfl
            wp_auto
            wp_for_post
            iframe
            iexists _, _, _
            iframe
            ipureintro
            refine ⟨⟨by word, by word⟩, ⟨by word, by word⟩, fun r h => ?_⟩
            rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word] at h
            have := Hacc (s ++ r) (by rw [Hdrop, Hdropk]; exact Hout _ _ h)
            simpa using this
        · -- no argument left
          wp_apply wp_arbitraryString as %junk -
          wp_for_post
          iapply HΦ
          iframe
          ipureintro
          refine Hacc junk ?_
          rw [Hdrop, show xs.drop (sint.nat k) = [] from List.drop_eq_nil_of_le (by word)]
          exact .other _ _ _ (not_simpleDirective_nil _ Hnp)
    · -- a byte other than `%`
      rw [Hc]
      wp_auto
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := w8) (t := go.byte) [c]
      wp_auto
      rw [show go.arrayLiteralSize
        [KeyedElement none (ElementExpression go.byte #c)] = 1 from rfl]
      isplitl []
      · ipureintro; rfl
      iintro %sl_ptr ⟨Hc_sl, -⟩
      wp_apply wp_bytes_to_string $$ Hc_sl as -
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ⟨by word, by word⟩, fun r h => ?_⟩
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word] at h
      have := Hacc (c :: r) (by rw [Hdrop]; exact .byte c _ _ _ Hif h)
      simpa using this
  · -- the end of the format
    have Hnot : ¬ sint.Z n < sint.Z (W64 format.length) := fun h => Hif (by rw [decide_eq_true h])
    simp only [decide_eq_false Hnot, Bool.false_eq_true, ↓reduceIte]
    rw [show sint.nat n = format.length by word, List.drop_length] at Hacc
    wp_auto
    wp_if_destruct
    · -- arguments are left
      wp_apply wp_arbitraryString as %junk -
      iapply HΦ
      iframe
      ipureintro
      refine Hacc junk ?_
      rw [List.drop_eq_getElem_cons (show sint.nat k < xs.length by word)]
      exact .extra _ _ _
    · iapply HΦ
      iframe
      ipureintro
      have := Hacc [] (by rw [List.drop_eq_nil_of_le (by word)]; exact .done)
      simpa using this

/-- `fmt.Printf(format, args...)` returns; the output is not modelled, nor the results. The
arguments `args_sl ↦*{dq} xs` must be of predeclared basic types (`ArgsWf`), as for
`wp_Sprintf`: Go calls the methods of other arguments, which the model does not. -/
theorem wp_Printf (format : GoString) (args_sl : GoSlice) (xs : List GoInterface) (dq : DFrac)
    (Hxs : ArgsWf xs) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs }}
      (App (App (Val (@! Printf)) (Val #format)) (Val #args_sl))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err); args_sl ↦*{dq} xs }} := by
  wp_start as Hsl
  iapply HΦ
  iframe

end wps

end fmt

end Perennial
end
