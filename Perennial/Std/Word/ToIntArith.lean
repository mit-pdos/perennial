/-
Facts about `toInt` of word arithmetic in a form that `omega` can use without
case splits (used by `word_sint_arith` in `Perennial/Std/Word/Automation.lean`).
The operands' signed values are given as `Int` terms `X`, `Y` (`x.toInt` itself,
or the value of a literal).
-/
module

public import Perennial.Std.Word

@[expose] public section

noncomputable section

namespace Perennial.word

variable {n : Nat}

/-- The range of `x.toInt`, without `n - 1`. -/
theorem toInt_range2 (x : BitVec n) : -(2 ^ n : Int) ≤ 2 * x.toInt ∧ 2 * x.toInt < 2 ^ n := by
  have := x.isLt
  have h : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
  rw [BitVec.toInt_eq_toNat_cond]; split <;> omega

theorem two_mul_lt_of_toInt_nonneg {x : BitVec n} (h : 0 ≤ x.toInt) : 2 * x.toNat < 2 ^ n := by
  have := x.isLt
  rw [BitVec.toInt_eq_toNat_cond] at h
  split at h
  · assumption
  · have : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by push_cast; rfl
    omega

theorem toInt_nonneg_toNat {x : BitVec n} (h : 0 ≤ x.toInt) : x.toInt = x.toNat :=
  BitVec.toInt_eq_toNat_of_lt (two_mul_lt_of_toInt_nonneg h)

theorem toInt_udiv_eq (x y : BitVec n) {X Y : Int} (hx : x.toInt = X) (hy : y.toInt = Y)
    (h : 0 ≤ X ∧ 0 < Y) : (x / y).toInt = X / Y := by
  have h1 := toInt_nonneg_toNat (x := x) (by omega)
  have h2 := toInt_nonneg_toNat (x := y) (by omega)
  have hm : x.msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt]; exact two_mul_lt_of_toInt_nonneg (by omega)
  rw [BitVec.toInt_udiv_of_msb hm, ← hx, ← hy, h1, h2]

theorem toInt_umod_eq (x y : BitVec n) {X Y : Int} (hx : x.toInt = X) (hy : y.toInt = Y)
    (h : 0 ≤ X ∧ 0 < Y) : (x % y).toInt = X % Y := by
  have h1 := toInt_nonneg_toNat (x := x) (by omega)
  have h2 := toInt_nonneg_toNat (x := y) (by omega)
  have hlt : (x % y).toNat ≤ x.toNat := by rw [BitVec.toNat_umod]; exact Nat.mod_le _ _
  have hx2 : 2 * x.toNat < 2 ^ n := two_mul_lt_of_toInt_nonneg (by omega)
  rw [BitVec.toInt_eq_toNat_of_lt (by omega), BitVec.toNat_umod, ← hx, ← hy, h1, h2]; rfl

theorem bmod_two_pow_of_range {z : Int} (h : -(2 ^ n : Int) ≤ 2 * z ∧ 2 * z < 2 ^ n) :
    z.bmod (2 ^ n) = z :=
  Int.bmod_eq_of_le_mul_two (by push_cast; omega) (by push_cast; omega)

theorem toInt_add_eq (x y : BitVec n) {X Y : Int} (hx : x.toInt = X) (hy : y.toInt = Y)
    (h : -(2 ^ n : Int) ≤ 2 * (X + Y) ∧ 2 * (X + Y) < 2 ^ n) : (x + y).toInt = X + Y := by
  rw [BitVec.toInt_add, hx, hy, bmod_two_pow_of_range h]

theorem toInt_sub_eq (x y : BitVec n) {X Y : Int} (hx : x.toInt = X) (hy : y.toInt = Y)
    (h : -(2 ^ n : Int) ≤ 2 * (X - Y) ∧ 2 * (X - Y) < 2 ^ n) : (x - y).toInt = X - Y := by
  rw [BitVec.toInt_sub, hx, hy, bmod_two_pow_of_range h]

theorem toInt_mul_eq (x y : BitVec n) {X Y : Int} (hx : x.toInt = X) (hy : y.toInt = Y)
    (h : -(2 ^ n : Int) ≤ 2 * (X * Y) ∧ 2 * (X * Y) < 2 ^ n) : (x * y).toInt = X * Y := by
  rw [BitVec.toInt_mul, hx, hy, bmod_two_pow_of_range h]

theorem toInt_neg_eq (x : BitVec n) {X : Int} (hx : x.toInt = X)
    (h : -(2 ^ n : Int) ≤ 2 * -X ∧ 2 * -X < 2 ^ n) : (-x).toInt = -X := by
  rw [BitVec.toInt_neg, hx, bmod_two_pow_of_range h]

theorem toInt_ofInt_eq (z : Int) (h : -(2 ^ n : Int) ≤ 2 * z ∧ 2 * z < 2 ^ n) :
    (BitVec.ofInt n z).toInt = z := by
  rw [BitVec.toInt_ofInt, bmod_two_pow_of_range h]

theorem toInt_ofNat_eq (k : Nat) (h : 2 * (k : Int) < 2 ^ n) :
    (BitVec.ofNat n k).toInt = k := by
  rw [BitVec.toInt_ofNat', bmod_two_pow_of_range ⟨by omega, h⟩]

/-! The side of the no-overflow condition that follows from the range of the
non-literal operand and the sign of the literal one. -/

theorem add_lo_r (x : BitVec n) {X Y : Int} (hx : x.toInt = X) (hY : 0 ≤ Y) :
    -(2 ^ n : Int) ≤ 2 * (X + Y) := by have := toInt_range2 x; omega
theorem add_hi_r (x : BitVec n) {X Y : Int} (hx : x.toInt = X) (hY : Y ≤ 0) :
    2 * (X + Y) < 2 ^ n := by have := toInt_range2 x; omega
theorem add_lo_l (y : BitVec n) {X Y : Int} (hy : y.toInt = Y) (hX : 0 ≤ X) :
    -(2 ^ n : Int) ≤ 2 * (X + Y) := by have := toInt_range2 y; omega
theorem add_hi_l (y : BitVec n) {X Y : Int} (hy : y.toInt = Y) (hX : X ≤ 0) :
    2 * (X + Y) < 2 ^ n := by have := toInt_range2 y; omega
theorem sub_hi_r (x : BitVec n) {X Y : Int} (hx : x.toInt = X) (hY : 0 ≤ Y) :
    2 * (X - Y) < 2 ^ n := by have := toInt_range2 x; omega
theorem sub_lo_r (x : BitVec n) {X Y : Int} (hx : x.toInt = X) (hY : Y ≤ 0) :
    -(2 ^ n : Int) ≤ 2 * (X - Y) := by have := toInt_range2 x; omega

theorem toNat_of_nonneg_eq {z : Int} (h : 0 ≤ z) : ((z.toNat : Nat) : Int) = z :=
  Int.toNat_of_nonneg h

theorem toNat_cases (z : Int) : (0 ≤ z ∧ ((z.toNat : Nat) : Int) = z) ∨ (z < 0 ∧ z.toNat = 0) := by
  by_cases h : 0 ≤ z
  · exact .inl ⟨h, Int.toNat_of_nonneg h⟩
  · exact .inr ⟨by omega, by omega⟩

end Perennial.word
