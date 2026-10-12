/-
Shared definitions of the proofs of the Go `fmt` package: its `isPkgInit`, `SprintfOut` (the
relation the result of `Sprintf` satisfies), the decimals its integer directives write, the
well-formedness of arguments (`ArgsWf`), and lemmas about them.
-/
module

public import Perennial.Proof.sync.Base
public import Perennial.Proof.io.Base
public import Perennial.Proof.errors.Base
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
end wps

end fmt

end Perennial
