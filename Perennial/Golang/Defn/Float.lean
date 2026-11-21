/-
IEEE 754 binary floating-point arithmetic, the semantics of Go's `float64` and
`float32` operations (`Float64Semantics`, `Float32Semantics` in
`Perennial/Golang/Defn/Predeclared.lean`). A float is its bit pattern
(`w64`/`w32`).

The definitions follow the standard's own terms (IEEE 754-2019): an operation
is computed "as if it first produced an intermediate result correct to infinite
precision and with unbounded range, and then rounded that intermediate result"
(§4.3). So each operation decodes its operands to an exact rational (or an
infinity, or NaN), applies the special cases of §6–§7 (NaN, infinities, signed
zeros, invalid operations, division by zero), and otherwise rounds the exact
rational result with `Format.round`: round to nearest, ties to even (§4.3.1),
on the subnormal grid below `2 ^ emin`, overflowing to an infinity (§7.4).
`round` is the only algorithmic part.

The definitions are written to be read and are computable, so that they can be
tested against Go (`docs/design/float/`), not to be fast. See
`docs/design/float-semantics.md` for the design.

**NaN results are not specified here.** Where IEEE 754 produces a NaN, these
functions return the fixed quiet NaN `Format.nan`, but its bits mean nothing: the
sign and payload of a NaN result are architecture-dependent (amd64's default NaN
has its sign bit set, arm64's does not), and the step rules replace every NaN
result of an operation by an arbitrary NaN (`go.float64Result`,
`go.float32Result`). Only "is a NaN" is meaningful.

**Fused multiply-add is not modelled.** The Go spec allows an implementation to
fuse operations, computing `x*y + z` with a single rounding (arm64, ppc64le,
s390x and riscv64 do), which can give a different result from the two
roundings here. Proofs about such code are about the unfused evaluation only.

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

/-- A floating-point datum (§3.2, level 2), the value of a bit pattern: NaN, an infinity, or a
finite number `±m` given by its sign (`neg`) and its exact magnitude `m ≥ 0` (a zero is
`finite neg 0`: `+0` and `-0`). -/
inductive Datum where
  | nan
  | inf (neg : Bool)
  | finite (neg : Bool) (m : Rat)

namespace Datum
/-- Negation: flips the sign (§5.5.1). -/
def neg : Datum → Datum
  | nan => nan
  | inf s => inf !s
  | finite s m => finite (!s) m
end Datum

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

def zero (s : Bool) : f.Bits := f.pack s 0 0
def inf (s : Bool) : f.Bits := f.pack s (2 ^ f.w - 1) 0
/-- A (quiet) NaN, returned where IEEE 754 produces a NaN; which one is immaterial (see the
module docstring). -/
def nan : f.Bits := f.pack false (2 ^ f.w - 1) (2 ^ (f.t - 1))

/-- The datum of a bit pattern (§3.4). -/
def decode (x : f.Bits) : Datum :=
  let s := x.msb
  let E := x.toNat / 2 ^ f.t % 2 ^ f.w
  let T := x.toNat % 2 ^ f.t
  if E = 2 ^ f.w - 1 then
    if T = 0 then .inf s else .nan
  else if E = 0 then
    .finite s (T * pow2 (f.emin - f.t))                   -- ±0 and subnormals: 0.T × 2^emin
  else
    .finite s ((2 ^ f.t + T) * pow2 (E - f.bias - f.t))  -- normal numbers: 1.T × 2^(E - bias)

/-- Rounding of the exact value `±m` (`m ≥ 0`, sign `s`) to the format: round to nearest, ties
to even (§4.3.1). `m` is scaled to an integer significand `M` at the exponent of `m`, clamped to
at least `emin` (below it, the subnormal grid of spacing `2 ^ (emin - t)`), and rounded;
a significand that rounds up to `2 ^ p` moves to the next exponent, and an exponent above
`emax` overflows to `±∞` (§7.4). A result that rounds to zero (`m = 0`, or underflow) is the
zero of sign `s` (§6.3). -/
def round (s : Bool) (m : Rat) : f.Bits :=
  if m = 0 then f.zero s else
  let e := max (floorLog2 m) f.emin
  let M := roundHalfEven (m * pow2 (f.t - e))   -- `m / 2 ^ (e - t)` rounded: `M ≤ 2 ^ (t + 1)`
  if M < 2 ^ f.t then f.pack s 0 M             -- subnormal or zero (`e = emin`)
  else if M = 2 ^ (f.t + 1) then               -- rounded up to `2 ^ (e + 1)`
    if f.emax < e + 1 then f.inf s else f.pack s (e + 1 + f.bias).toNat 0
  else if f.emax < e then f.inf s else f.pack s (e + f.bias).toNat (M - 2 ^ f.t)

/-- Rounding of a rational `q`; a zero `q` is `+0`. -/
def roundRat (q : Rat) : f.Bits := f.round (decide (q < 0)) (if q < 0 then -q else q)

/-- Addition of two data (§5.4.1, §6.1–§6.3, §7.2). -/
def addDatum : Datum → Datum → f.Bits
  | .nan, _ | _, .nan => f.nan
  | .inf s, .inf s' => if s = s' then f.inf s else f.nan     -- `∞ - ∞` is invalid
  | .inf s, .finite .. | .finite .., .inf s => f.inf s
  | .finite s m, .finite s' m' =>
    let r := signed s m + signed s' m'
    -- an exact zero sum is `+0` (in round to nearest), except `(-0) + (-0) = -0`
    if r = 0 then f.zero (s && s') else f.roundRat r

def addDef (x y : f.Bits) : f.Bits := f.addDatum (f.decode x) (f.decode y)

/-- `x - y` is `x + (-y)` (§5.4.1). -/
def subDef (x y : f.Bits) : f.Bits := f.addDatum (f.decode x) (f.decode y).neg

/-- Multiplication (§5.4.1, §6.1, §6.3, §7.2). The sign of a product is the exclusive or of
the operands' signs, also for a zero or infinite product. -/
def mulDef (x y : f.Bits) : f.Bits :=
  match f.decode x, f.decode y with
  | .nan, _ | _, .nan => f.nan
  | .inf s, .inf s' => f.inf (s ^^ s')
  | .inf s, .finite s' m | .finite s' m, .inf s =>
    if m = 0 then f.nan else f.inf (s ^^ s')                -- `0 × ∞` is invalid
  | .finite s m, .finite s' m' => f.round (s ^^ s') (m * m')

/-- Division (§5.4.1, §6.1, §6.3, §7.2, §7.3). The sign of a quotient is the exclusive or of
the operands' signs. -/
def divDef (x y : f.Bits) : f.Bits :=
  match f.decode x, f.decode y with
  | .nan, _ | _, .nan => f.nan
  | .inf _, .inf _ => f.nan                                -- `∞ / ∞` is invalid
  | .inf s, .finite s' _ => f.inf (s ^^ s')
  | .finite s _, .inf s' => f.zero (s ^^ s')
  | .finite s m, .finite s' m' =>
    if m' = 0 then
      if m = 0 then f.nan else f.inf (s ^^ s')           -- `0 / 0` is invalid; division by zero
    else f.round (s ^^ s') (m / m')

/-- Negation flips the sign bit (§5.5.1); of a NaN, it is a NaN. -/
def negDef (x : f.Bits) : f.Bits :=
  match f.decode x with
  | .nan => f.nan
  | _ => x ^^^ BitVec.twoPow _ (f.w + f.t)

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

def isNaNDef (x : f.Bits) : Bool :=
  match f.decode x with
  | .nan => true
  | _ => false

/-- The conversion of an integer (§5.4.1 convertFromInt): its rounding. -/
def ofIntDef (n : Int) : f.Bits := f.roundRat n

/-- The conversion to format `g` (§5.4.1 formatOf-convertFormat): the rounding of the value. -/
def convertDef (g : Format) (x : f.Bits) : g.Bits :=
  match f.decode x with
  | .nan => g.nan
  | .inf s => g.inf s
  | .finite s m => g.round s m

@[irreducible] def add (x y : f.Bits) : f.Bits := f.addDef x y
@[irreducible] def sub (x y : f.Bits) : f.Bits := f.subDef x y
@[irreducible] def mul (x y : f.Bits) : f.Bits := f.mulDef x y
@[irreducible] def div (x y : f.Bits) : f.Bits := f.divDef x y
@[irreducible] def neg (x : f.Bits) : f.Bits := f.negDef x
@[irreducible] def leb (x y : f.Bits) : Bool := f.lebDef x y
@[irreducible] def eq (x y : f.Bits) : Bool := f.eqDef x y
@[irreducible] def isNaN (x : f.Bits) : Bool := f.isNaNDef x
@[irreducible] def ofInt (n : Int) : f.Bits := f.ofIntDef n
@[irreducible] def convert (g : Format) (x : f.Bits) : g.Bits := f.convertDef g x

theorem add_unseal : f.add = f.addDef := by with_unfolding_all rfl
theorem sub_unseal : f.sub = f.subDef := by with_unfolding_all rfl
theorem mul_unseal : f.mul = f.mulDef := by with_unfolding_all rfl
theorem div_unseal : f.div = f.divDef := by with_unfolding_all rfl
theorem neg_unseal : f.neg = f.negDef := by with_unfolding_all rfl
theorem leb_unseal : f.leb = f.lebDef := by with_unfolding_all rfl
theorem eq_unseal : f.eq = f.eqDef := by with_unfolding_all rfl
theorem isNaN_unseal : f.isNaN = f.isNaNDef := by with_unfolding_all rfl
theorem ofInt_unseal : f.ofInt = f.ofIntDef := by with_unfolding_all rfl
theorem convert_unseal : f.convert = f.convertDef := by with_unfolding_all rfl

end Format
end ieee754

open ieee754

/-! ## The operations of `float64` and `float32`

A float is its bit pattern; `binary64.Bits` is `w64` and `binary32.Bits` is `w32`. -/

def float64Neg (x : w64) : w64 := binary64.neg x
def float64Add (x y : w64) : w64 := binary64.add x y
def float64Sub (x y : w64) : w64 := binary64.sub x y
def float64Mul (x y : w64) : w64 := binary64.mul x y
def float64Div (x y : w64) : w64 := binary64.div x y
def float64Leb (x y : w64) : Bool := binary64.leb x y
def float64Eq (x y : w64) : Bool := binary64.eq x y
def float64IsNaN (x : w64) : Bool := binary64.isNaN x
/-- A NaN of type `float64` (that of Go's `math.NaN()`, `0x7FF8000000000001`). -/
def float64NaN : w64 := 0x7FF8000000000001

def float32Neg (x : w32) : w32 := binary32.neg x
def float32Add (x y : w32) : w32 := binary32.add x y
def float32Sub (x y : w32) : w32 := binary32.sub x y
def float32Mul (x y : w32) : w32 := binary32.mul x y
def float32Div (x y : w32) : w32 := binary32.div x y
def float32Leb (x y : w32) : Bool := binary32.leb x y
def float32Eq (x y : w32) : Bool := binary32.eq x y
def float32IsNaN (x : w32) : Bool := binary32.isNaN x
/-- A NaN of type `float32` (`float32(math.NaN())`, `0x7FC00000`). -/
def float32NaN : w32 := 0x7FC00000

/-- `float32(x)` of a `float64`. -/
def float64ToFloat32 (x : w64) : w32 := binary64.convert binary32 x

/-- `float64(n)` of an integer (`int64`, `uint64`, `int32`, `uint32`). -/
def int64ToFloat64 (n : w64) : w64 := binary64.ofInt n.toInt
def uint64ToFloat64 (n : w64) : w64 := binary64.ofInt n.toNat
def int32ToFloat64 (n : w32) : w64 := binary64.ofInt n.toInt
def uint32ToFloat64 (n : w32) : w64 := binary64.ofInt n.toNat

end Perennial
