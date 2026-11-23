/-
IEEE 754 binary floating-point arithmetic, the semantics of Go's `float64` and
`float32` operations (`Float64Semantics`, `Float32Semantics` in
`Perennial/Golang/Defn/Predeclared.lean`). A float is its bit pattern
(`w64`/`w32`).

The definitions follow the standard's own terms (IEEE 754-2019): an operation
is computed "as if it first produced an intermediate result correct to infinite
precision and with unbounded range, and then rounded that intermediate result"
(§4.3). So an operation works on exact values (`FloatValue`: NaN, `±∞`, or a finite
number as a sign and an exact rational magnitude), not on bits: it decodes its operands
(`Format.decode`), applies the special cases of §6–§7 (NaN, infinities, signed
zeros, invalid operations, division by zero), and otherwise rounds the exact
rational result (`Format.round`: round to nearest, ties to even (§4.3.1), on the
subnormal grid below `2 ^ emin`, overflowing to an infinity (§7.4)). Its result
is a `FloatValue`. Encoding it as bits is a separate step (`Format.encode`,
`Format.encodes`).

The definitions are written to be read and are computable, so that they can be
tested against Go (`docs/design/float/`), not to be fast. See
`docs/design/float-semantics.md` for the design.

**A NaN has no particular encoding.** Every value but NaN has exactly one bit
pattern (`encode`); NaN has many, and `encodes .nan b` holds of every NaN `b`.
The sign and payload of a NaN result are architecture-dependent (amd64's default
NaN has its sign bit set, arm64's does not), so the step rules let an operation
whose result is NaN step to any NaN (`float64Encodes`, `float32Encodes`).

**Fused multiply-add is not modelled.** The Go spec allows an implementation to
fuse operations, computing `x*y + z` with a single rounding (gc does on arm64),
which can give a different result from the two roundings here. Proofs about such
code are about the unfused evaluation only.

The operations are sealed (`@[irreducible]`, `foo_unseal`) so that automation
does not unfold rounding in unrelated proofs.
-/
module

public import Perennial.Std.Word

@[expose] public section

namespace Perennial
namespace ieee754

/-- `2 ^ k` as a rational, for an integer `k`. -/
def pow2 (k : Int) : Rat :=
  if 0 ≤ k then ((2 ^ k.toNat : Nat) : Rat) else (((2 ^ (-k).toNat : Nat) : Rat))⁻¹

/-- `⌊log₂ a⌋` for `a > 0`: the `e` with `2 ^ e ≤ a < 2 ^ (e + 1)`. (If `a = n / d` with
`2 ^ i ≤ n < 2 ^ (i + 1)` and `2 ^ j ≤ d < 2 ^ (j + 1)`, then `2 ^ (i-j-1) < a < 2 ^ (i-j+1)`.) -/
def floorLog2 (a : Rat) : Int :=
  let e : Int := (a.num.toNat.log2 : Int) - (a.den.log2 : Int)
  if pow2 e ≤ a then e else e - 1

/-- The integer nearest to `x ≥ 0`, ties to even. -/
def roundHalfEven (x : Rat) : Nat :=
  let n := x.floor
  let r := x - n
  (if r < 1/2 ∨ (r = 1/2 ∧ n % 2 = 0) then n else n + 1).toNat

/-- The exact value of a float operation's result: NaN, a signed infinity, or a finite number
`±m` given by its sign (`neg`) and its exact rational magnitude `m ≥ 0` (a zero is
`finite neg 0`: `+0` and `-0`). It corresponds roughly to IEEE 754's level-2 "floating-point
data" (§3.2), except that `finite` may also hold magnitudes that the format cannot represent:
only the results of `decode` and `round` are representable, which is why `encode` is only
meaningful on those. -/
inductive FloatValue where
  | nan
  | inf (neg : Bool)
  | finite (neg : Bool) (m : Rat)
deriving DecidableEq

namespace FloatValue
/-- Negation: flips the sign (§5.5.1). -/
def neg : FloatValue → FloatValue
  | nan => nan
  | inf s => inf !s
  | finite s m => finite (!s) m
end FloatValue

/-- `±m`, the rational value of a sign and a magnitude. -/
def signed (neg : Bool) (m : Rat) : Rat := if neg then -m else m

/-- A binary interchange format (§3.6): `w` bits of biased exponent and `t` bits of trailing
significand, so precision `p = t + 1`, `emax = 2 ^ (w - 1) - 1`, `emin = 1 - emax`. -/
structure Format where
  w : Nat
  t : Nat

/-- binary64 (`float64`): `p = 53`, `emin = -1022`, `emax = 1023`. -/
def binary64 : Format := ⟨11, 52⟩
/-- binary32 (`float32`): `p = 24`, `emin = -126`, `emax = 127`. -/
def binary32 : Format := ⟨8, 23⟩

namespace Format
variable (f : Format)

def emax : Int := ((2 ^ (f.w - 1) : Nat) : Int) - 1
def emin : Int := 1 - f.emax
def bias : Int := f.emax

/-- A bit pattern of the format: sign bit, biased exponent, trailing significand (§3.4). -/
abbrev Bits := BitVec (1 + f.w + f.t)

/-- The bit pattern with sign `s`, biased exponent `E` and trailing significand `T`. -/
def pack (s : Bool) (E T : Nat) : f.Bits :=
  BitVec.ofBool s ++ BitVec.ofNat f.w E ++ BitVec.ofNat f.t T

/-- The value of a bit pattern (§3.4). -/
def decode (x : f.Bits) : FloatValue :=
  let s := x.msb
  let E := x.toNat / 2 ^ f.t % 2 ^ f.w
  let T := x.toNat % 2 ^ f.t
  if E = 2 ^ f.w - 1 then
    if T = 0 then .inf s else .nan
  else if E = 0 then
    .finite s (T * pow2 (f.emin - f.t))                   -- ±0 and subnormals: 0.T × 2^emin
  else
    .finite s ((2 ^ f.t + T) * pow2 (E - f.bias - f.t))  -- normal numbers: 1.T × 2^(E - bias)

/-- The bit pattern of a value representable in the format, the inverse of `decode`; NaN has
many bit patterns, hence `none`. A finite `m` is `M × 2 ^ (e - t)` with an integer significand
`M`, at the exponent `e` of `m` clamped to at least `emin`: subnormal (or zero) if `M < 2 ^ t`,
normal otherwise.

**Precondition: the value is representable in `f`** (NaN, `±∞`, or a finite value that some bit
pattern of `f` decodes to). `encode` does not check it: on a finite value that `f` cannot
represent (a magnitude off the format's grid, or `2 ^ (emax + 1)` or more) it still returns
`some` bits, and those bits mean nothing (they need not decode to the value, or to anything
near it).

This is sound where `encode` is used, because it is only ever applied to values that are
representable by construction: the results of the operations above (`add`, `sub`, `mul`, `div`,
`neg`, `ofInt`, `ofConst`, `convert` to `f`), each of which is NaN, an infinity, a signed zero, the
negation of a `decode` result, or a `round` result in `f` (whose finite results are on `f`'s
grid and below `2 ^ (emax + 1)`, by the definition of `round`). The step rules reach `encode`
only through `encodes` (`float64Encodes`, `float32Encodes`) on those results, and the
conversions below only on `ofInt` and `ofConst` results. The test vectors in
`docs/design/float/` check against Go that the bits are right on such results. -/
def encode : FloatValue → Option f.Bits
  | .nan => none
  | .inf s => some (f.pack s (2 ^ f.w - 1) 0)
  | .finite s m =>
    let e := max (floorLog2 m) f.emin
    let M := (m * pow2 (f.t - e)).floor.toNat
    if M < 2 ^ f.t then some (f.pack s 0 M)
    else some (f.pack s (e + f.bias).toNat (M - 2 ^ f.t))

/-- `b` encodes the value `d`: `b` is `d`'s bit pattern, or any NaN if `d` is NaN. -/
def encodes (d : FloatValue) (b : f.Bits) : Prop :=
  match f.encode d with
  | some b' => b = b'
  | none => f.decode b = .nan

/-- Rounding of the exact value `±m` (`m ≥ 0`, sign `s`) to the format: round to nearest, ties
to even (§4.3.1). `m` is scaled to an integer significand at the exponent of `m`, clamped to
at least `emin` (below it, the subnormal grid of spacing `2 ^ (emin - t)`), and rounded; a
magnitude that rounds to `2 ^ (emax + 1)` or more overflows to `±∞` (§7.4). A result that
rounds to zero (`m = 0`, or underflow) is the zero of sign `s` (§6.3). -/
def round (s : Bool) (m : Rat) : FloatValue :=
  let e := max (floorLog2 m) f.emin
  let r := roundHalfEven (m * pow2 (f.t - e)) * pow2 (e - f.t)   -- the rounded magnitude
  if r < pow2 (f.emax + 1) then .finite s r else .inf s

/-- Rounding of a rational `q`; a zero `q` is `+0`. -/
def roundRat (q : Rat) : FloatValue := f.round (decide (q < 0)) (if q < 0 then -q else q)

/-- Addition of two values (§5.4.1, §6.1–§6.3, §7.2). -/
def addValue : FloatValue → FloatValue → FloatValue
  | .nan, _ | _, .nan => .nan
  | .inf s, .inf s' => if s = s' then .inf s else .nan      -- `∞ - ∞` is invalid
  | .inf s, .finite .. | .finite .., .inf s => .inf s
  | .finite s m, .finite s' m' =>
    let r := signed s m + signed s' m'
    -- an exact zero sum is `+0` (in round to nearest), except `(-0) + (-0) = -0`
    if r = 0 then .finite (s && s') 0 else f.roundRat r

def addDef (x y : f.Bits) : FloatValue := f.addValue (f.decode x) (f.decode y)

/-- `x - y` is `x + (-y)` (§5.4.1). -/
def subDef (x y : f.Bits) : FloatValue := f.addValue (f.decode x) (f.decode y).neg

/-- Multiplication (§5.4.1, §6.1, §6.3, §7.2). The sign of a product is the exclusive or of
the operands' signs, also for a zero or infinite product. -/
def mulDef (x y : f.Bits) : FloatValue :=
  match f.decode x, f.decode y with
  | .nan, _ | _, .nan => .nan
  | .inf s, .inf s' => .inf (s ^^ s')
  | .inf s, .finite s' m | .finite s' m, .inf s =>
    if m = 0 then .nan else .inf (s ^^ s')                  -- `0 × ∞` is invalid
  | .finite s m, .finite s' m' => f.round (s ^^ s') (m * m')

/-- Division (§5.4.1, §6.1, §6.3, §7.2, §7.3). The sign of a quotient is the exclusive or of
the operands' signs. -/
def divDef (x y : f.Bits) : FloatValue :=
  match f.decode x, f.decode y with
  | .nan, _ | _, .nan => .nan
  | .inf _, .inf _ => .nan                                 -- `∞ / ∞` is invalid
  | .inf s, .finite s' _ => .inf (s ^^ s')
  | .finite s _, .inf s' => .finite (s ^^ s') 0
  | .finite s m, .finite s' m' =>
    if m' = 0 then
      if m = 0 then .nan else .inf (s ^^ s')             -- `0 / 0` is invalid; division by zero
    else f.round (s ^^ s') (m / m')

/-- Negation flips the sign (§5.5.1); of a NaN, it is NaN. -/
def negDef (x : f.Bits) : FloatValue := (f.decode x).neg

/-- `x ≤ y` (§5.11): NaN is unordered with everything; `-0 = +0`. -/
def lebDef (x y : f.Bits) : Bool :=
  match f.decode x, f.decode y with
  | .nan, _ | _, .nan => false
  | .inf s, .inf s' => s || !s'                            -- `-∞ ≤ y`; `+∞ ≤ +∞`
  | .inf s, .finite .. => s
  | .finite .., .inf s' => !s'
  | .finite s m, .finite s' m' => decide (signed s m ≤ signed s' m')

/-- `x == y` (§5.11): NaN is unordered with everything (`NaN != NaN`); `-0 == +0`. -/
def eqDef (x y : f.Bits) : Bool :=
  match f.decode x, f.decode y with
  | .inf s, .inf s' => s == s'
  | .finite s m, .finite s' m' => decide (signed s m = signed s' m')
  | _, _ => false

def isNaNDef (x : f.Bits) : Bool := f.decode x == .nan

/-- The conversion of an integer (§5.4.1 convertFromInt): its rounding. -/
def ofIntDef (n : Int) : FloatValue := f.roundRat n

/-- The value of a Go constant whose exact value is `q`: its rounding, except that a constant
that rounds to zero is `+0` (a Go constant is never a negative zero). -/
def ofConstDef (q : Rat) : FloatValue :=
  if f.roundRat q = .finite true 0 then .finite false 0 else f.roundRat q

/-- The conversion to format `g` (§5.4.1 formatOf-convertFormat): the rounding of the value. -/
def convertDef (g : Format) (x : f.Bits) : FloatValue :=
  match f.decode x with
  | .finite s m => g.round s m
  | d => d

@[irreducible] def add (x y : f.Bits) : FloatValue := f.addDef x y
@[irreducible] def sub (x y : f.Bits) : FloatValue := f.subDef x y
@[irreducible] def mul (x y : f.Bits) : FloatValue := f.mulDef x y
@[irreducible] def div (x y : f.Bits) : FloatValue := f.divDef x y
@[irreducible] def neg (x : f.Bits) : FloatValue := f.negDef x
@[irreducible] def leb (x y : f.Bits) : Bool := f.lebDef x y
@[irreducible] def eq (x y : f.Bits) : Bool := f.eqDef x y
@[irreducible] def isNaN (x : f.Bits) : Bool := f.isNaNDef x
@[irreducible] def ofInt (n : Int) : FloatValue := f.ofIntDef n
@[irreducible] def ofConst (q : Rat) : FloatValue := f.ofConstDef q
@[irreducible] def convert (g : Format) (x : f.Bits) : FloatValue := f.convertDef g x

theorem add_unseal : f.add = f.addDef := by with_unfolding_all rfl
theorem sub_unseal : f.sub = f.subDef := by with_unfolding_all rfl
theorem mul_unseal : f.mul = f.mulDef := by with_unfolding_all rfl
theorem div_unseal : f.div = f.divDef := by with_unfolding_all rfl
theorem neg_unseal : f.neg = f.negDef := by with_unfolding_all rfl
theorem leb_unseal : f.leb = f.lebDef := by with_unfolding_all rfl
theorem eq_unseal : f.eq = f.eqDef := by with_unfolding_all rfl
theorem isNaN_unseal : f.isNaN = f.isNaNDef := by with_unfolding_all rfl
theorem ofInt_unseal : f.ofInt = f.ofIntDef := by with_unfolding_all rfl
theorem ofConst_unseal : f.ofConst = f.ofConstDef := by with_unfolding_all rfl
theorem convert_unseal : f.convert = f.convertDef := by with_unfolding_all rfl

end Format
end ieee754

open ieee754

/-! ## The operations of `float64` and `float32`

A float is its bit pattern; `binary64.Bits` is `w64` and `binary32.Bits` is `w32`. An
arithmetic operation's result is a `FloatValue`, which the step rules encode
(`float64Encodes`): its bit pattern, or any NaN. -/

/-- `b` encodes the `float64` value `d`: its bit pattern, or any NaN if `d` is NaN. -/
def float64Encodes (d : FloatValue) (b : w64) : Prop := binary64.encodes d b
/-- `b` encodes the `float32` value `d`: its bit pattern, or any NaN if `d` is NaN. -/
def float32Encodes (d : FloatValue) (b : w32) : Prop := binary32.encodes d b

def float64Neg (x : w64) : FloatValue := binary64.neg x
def float64Add (x y : w64) : FloatValue := binary64.add x y
def float64Sub (x y : w64) : FloatValue := binary64.sub x y
def float64Mul (x y : w64) : FloatValue := binary64.mul x y
def float64Div (x y : w64) : FloatValue := binary64.div x y
def float64Leb (x y : w64) : Bool := binary64.leb x y
def float64Eq (x y : w64) : Bool := binary64.eq x y
def float64IsNaN (x : w64) : Bool := binary64.isNaN x

def float32Neg (x : w32) : FloatValue := binary32.neg x
def float32Add (x y : w32) : FloatValue := binary32.add x y
def float32Sub (x y : w32) : FloatValue := binary32.sub x y
def float32Mul (x y : w32) : FloatValue := binary32.mul x y
def float32Div (x y : w32) : FloatValue := binary32.div x y
def float32Leb (x y : w32) : Bool := binary32.leb x y
def float32Eq (x y : w32) : Bool := binary32.eq x y
def float32IsNaN (x : w32) : Bool := binary32.isNaN x

/-- `float32(x)` of a `float64` `x`, and `float64(x)` of a `float32` `x`. -/
def float64ToFloat32 (x : w64) : FloatValue := binary64.convert binary32 x
def float32ToFloat64 (x : w32) : FloatValue := binary32.convert binary64 x

/-! Conversions that never produce a NaN, as bits. (`getD 0` is never used: a rounding is
never NaN.) -/

/-- `float64(c)` (`float32(c)`) of a constant `c` whose exact value is `q`: its rounding, once
(`ofConst`). Also the one integer-to-float rounding: `float64(n)`/`float32(n)` of an integer `n`
of any type, or of an untyped integer constant, is `ratToFloat64 n`/`ratToFloat32 n` (for an
integer, `ofConst` is `ofInt`: an integer never rounds to `-0`). -/
def ratToFloat64 (q : Rat) : w64 := (binary64.encode (binary64.ofConst q)).getD 0
def ratToFloat32 (q : Rat) : w32 := (binary32.encode (binary32.ofConst q)).getD 0

/-- `float64(n)` of an integer (`int64`, `uint64`, `int32`, `uint32`): its rounding,
`ratToFloat64`. -/
def int64ToFloat64 (n : w64) : w64 := ratToFloat64 n.toInt
def uint64ToFloat64 (n : w64) : w64 := ratToFloat64 n.toNat
def int32ToFloat64 (n : w32) : w64 := ratToFloat64 n.toInt
def uint32ToFloat64 (n : w32) : w64 := ratToFloat64 n.toNat

end Perennial
