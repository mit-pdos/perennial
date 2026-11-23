/-
Facts about the IEEE 754 float operations of the Go semantics
(`Perennial/Golang/Defn/Float.lean`): signs of conversions and comparisons with zero, and the
specs of the arithmetic operations (IEEE 754's result, any NaN if it is a NaN), and exact
doubling of normal `float64`s (over the laws of `pow2` and `floorLog2`).
-/
module

public import Perennial.Golang.Defn.Float
public import Perennial.Golang.Theory.Auto

@[expose] public section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

namespace ieee754
namespace Format
variable (f : Format)

theorem msb_pack (s : Bool) (E T : Nat) : (f.pack s E T).msb = s := by
  simp [pack, BitVec.msb_append]

/-- A rounding has the sign it is given: it is `±∞` or a finite number of that sign. -/
theorem round_cases (s : Bool) (m : Rat) :
    f.round s m = .inf s ∨ ∃ r, f.round s m = .finite s r := by
  unfold round
  dsimp only
  split
  · exact .inr ⟨_, rfl⟩
  · exact .inl rfl

/-- The bit pattern of a rounding has the rounding's sign. -/
theorem msb_encode_round (s : Bool) (m : Rat) (b : f.Bits)
    (h : f.encode (f.round s m) = some b) : b.msb = s := by
  rcases f.round_cases s m with hr | ⟨r, hr⟩ <;> rw [hr] at h <;> simp only [encode] at h
  · cases h; exact f.msb_pack ..
  · split at h <;> (cases h; exact f.msb_pack ..)

theorem msb_encode_ofInt_of_nonneg (n : Int) (h : 0 ≤ n) :
    ((f.encode (f.ofInt n)).getD 0).msb = false := by
  have : ¬ (n : Rat) < 0 := fun h' => (Rat.not_le.mpr h') (by exact_mod_cast h)
  rw [ofInt_unseal, ofIntDef, roundRat]
  simp only [this, decide_false, if_false]
  cases hb : f.encode (f.round false n) with
  | none => simp
  | some b => exact f.msb_encode_round false _ b hb

/-- The rounding of a non-negative constant has a clear sign bit (it is `+0`, positive or
`+∞`). -/
theorem msb_encode_ofConst_of_nonneg (q : Rat) (h : 0 ≤ q) :
    ((f.encode (f.ofConst q)).getD 0).msb = false := by
  have hq : ¬ q < 0 := Rat.not_lt.mpr h
  rw [ofConst_unseal, ofConstDef]
  split
  · cases hb : f.encode (.finite false 0) with
    | none => simp
    | some b =>
      simp only [encode] at hb
      split at hb <;> (cases hb; exact f.msb_pack ..)
  · rw [roundRat]
    simp only [hq, decide_false, if_false]
    cases hb : f.encode (f.round false q) with
    | none => simp
    | some b => exact f.msb_encode_round false _ b hb

theorem pow2_nonneg (k : Int) : 0 ≤ pow2 k := by
  unfold pow2
  split
  · exact Rat.natCast_nonneg
  · exact Rat.le_of_lt (Rat.inv_pos.mpr (by
      have : (0 : Nat) < 2 ^ (-k).toNat := Nat.two_pow_pos _
      exact_mod_cast this))

/-- The value of a bit pattern with a clear sign bit: NaN, `+∞`, or a non-negative number. -/
theorem decode_of_msb_false (x : f.Bits) (h : x.msb = false) :
    f.decode x = .nan ∨ f.decode x = .inf false ∨ ∃ m, 0 ≤ m ∧ f.decode x = .finite false m := by
  unfold decode
  simp only [h]
  split
  · split
    · exact .inr (.inl rfl)
    · exact .inl rfl
  · split
    · exact .inr (.inr ⟨_, Rat.mul_nonneg Rat.natCast_nonneg (pow2_nonneg _), rfl⟩)
    · exact .inr (.inr ⟨_,
        Rat.mul_nonneg (by exact_mod_cast Rat.natCast_nonneg) (pow2_nonneg _), rfl⟩)

end Format
end ieee754

open ieee754

private theorem msb_false_of_toInt_nonneg {n : Nat} (x : BitVec n) (h : 0 ≤ x.toInt) :
    x.msb = false := by
  cases hm : x.msb
  · rfl
  · exact absurd (BitVec.toInt_neg_iff.mpr (BitVec.msb_eq_true_iff_two_mul_ge.mp hm)) (by omega)

/-! The sign facts that `counter.Add(v)`'s `v < 0` test needs (prometheus): `float64(n)` of a
non-negative integer has a clear sign bit (it is `+0` or positive), and a `float64` with a
clear sign bit (`+0`, a positive number, `+∞` or a NaN) is not below `+0`. -/

theorem int64ToFloat64_sign_clear (n : w64) (h : 0 ≤ sint.Z n) : 0 ≤ sint.Z (int64ToFloat64 n) :=
  BitVec.toInt_nonneg_of_msb_false (binary64.msb_encode_ofConst_of_nonneg _ (by exact_mod_cast h))
theorem uint64ToFloat64_sign_clear (n : w64) : 0 ≤ sint.Z (uint64ToFloat64 n) :=
  BitVec.toInt_nonneg_of_msb_false (binary64.msb_encode_ofConst_of_nonneg _ (by exact_mod_cast Nat.zero_le _))
theorem int32ToFloat64_sign_clear (n : w32) (h : 0 ≤ sint.Z n) : 0 ≤ sint.Z (int32ToFloat64 n) :=
  BitVec.toInt_nonneg_of_msb_false (binary64.msb_encode_ofConst_of_nonneg _ (by exact_mod_cast h))
theorem uint32ToFloat64_sign_clear (n : w32) : 0 ≤ sint.Z (uint32ToFloat64 n) :=
  BitVec.toInt_nonneg_of_msb_false (binary64.msb_encode_ofConst_of_nonneg _ (by exact_mod_cast Nat.zero_le _))

private theorem decode_zero64 : binary64.decode (W64 0) = .finite false 0 := by
  simp [Format.decode, binary64]

/-- `x < 0` (as `lt_float64` steps it: `Leb && !Eq`) is false for a `float64` `x` with a clear
sign bit. -/
theorem lt_zero_false_of_sign_clear (x : w64) (h : 0 ≤ sint.Z x) :
    (float64Leb x (W64 0) && !float64Eq x (W64 0)) = false := by
  have hd := binary64.decode_of_msb_false x (msb_false_of_toInt_nonneg x h)
  simp only [float64Leb, float64Eq, Format.leb_unseal, Format.eq_unseal, Format.lebDef,
    Format.eqDef, decode_zero64]
  rcases hd with hd | hd | ⟨m, hm, hd⟩ <;> rw [hd]
  · rfl
  · rfl
  · simp only [signed]
    by_cases h0 : m = 0
    · subst h0; decide
    · have : ¬ m ≤ 0 := fun h' => h0 (Rat.le_antisymm h' hm)
      simp [this]

/-- `x == x` unless `x` is a NaN. -/
theorem float64Eq_self (x : w64) : float64Eq x x = !float64IsNaN x := by
  simp only [float64Eq, float64IsNaN, Format.eq_unseal, Format.isNaN_unseal, Format.eqDef,
    Format.isNaNDef]
  cases binary64.decode x <;> simp

theorem float32Eq_self (x : w32) : float32Eq x x = !float32IsNaN x := by
  simp only [float32Eq, float32IsNaN, Format.eq_unseal, Format.isNaN_unseal, Format.eqDef,
    Format.isNaNDef]
  cases binary32.decode x <;> simp

/-- Every value has an encoding (NaN has many). -/
theorem float64Encodes_exists (d : FloatValue) : ∃ b, float64Encodes d b := by
  unfold float64Encodes Format.encodes
  cases h : binary64.encode d with
  | some b => exact ⟨b, rfl⟩
  | none => exact ⟨0x7FF8000000000000, by simp only; decide⟩
theorem float32Encodes_exists (d : FloatValue) : ∃ b, float32Encodes d b := by
  unfold float32Encodes Format.encodes
  cases h : binary32.encode d with
  | some b => exact ⟨b, rfl⟩
  | none => exact ⟨0x7FC00000, by simp only; decide⟩

/-- The encoding of a value that is not a NaN is its bit pattern. (The premise is a `==`, so that
`decide +kernel` proves it of a closed value.) -/
theorem float64Encodes_eq {d : FloatValue} {b f : w64} (h : (binary64.encode d == some b) = true)
    (hf : float64Encodes d f) : f = b := by
  simp only [float64Encodes, Format.encodes, eq_of_beq h] at hf; exact hf
theorem float32Encodes_eq {d : FloatValue} {b f : w32} (h : (binary32.encode d == some b) = true)
    (hf : float32Encodes d f) : f = b := by
  simp only [float32Encodes, Format.encodes, eq_of_beq h] at hf; exact hf

/-! ## Powers of two, `floorLog2`, and exact doubling

`pow2` is a group homomorphism from `Int` to the positive rationals (`pow2_add`, `pow2_pos`) and
strictly monotone (`pow2_lt`); `floorLog2 a` is characterized by `2 ^ e ≤ a < 2 ^ (e + 1)`
(`floorLog2_eq`). Over them, multiplying a normal `float64` by `2.0` is exact while the product
stays normal: its bits are `x`'s plus `2 ^ 52`, one more in the biased exponent
(`float64Mul_two_normal`). -/

namespace ieee754

theorem pow2_natCast (n : Nat) : pow2 (n : Int) = ((2 ^ n : Nat) : Rat) := by
  simp [pow2]

theorem pow2_zero : pow2 0 = 1 := by simp [pow2]

theorem pow2_neg_succ (n : Nat) :
    pow2 (-((n : Int) + 1)) = (((2 ^ (n + 1) : Nat) : Rat))⁻¹ := by
  unfold pow2
  simp only [show ¬ (0 ≤ -((n : Int) + 1)) by omega, ↓reduceIte]
  congr

theorem pow2_pos (k : Int) : 0 < pow2 k := by
  unfold pow2
  have h : ∀ n : Nat, (0 : Rat) < ((2 ^ n : Nat) : Rat) := fun n => by
    have : (0 : Nat) < 2 ^ n := Nat.two_pow_pos _
    exact_mod_cast this
  split
  · exact h _
  · exact Rat.inv_pos.mpr (h _)

theorem pow2_succ (k : Int) : pow2 (k + 1) = 2 * pow2 k := by
  rcases Int.lt_or_le k 0 with hk | hk
  · obtain ⟨n, hn⟩ : ∃ n : Nat, k = -((n : Int) + 1) := ⟨(-k - 1).toNat, by omega⟩
    subst hn
    rw [pow2_neg_succ]
    cases n with
    | zero =>
      rw [show -(((0 : Nat) : Int) + 1) + 1 = ((0 : Nat) : Int) by omega, pow2_natCast]
      decide +kernel
    | succ n =>
      rw [show -(((n + 1 : Nat) : Int) + 1) + 1 = -((n : Int) + 1) by omega, pow2_neg_succ]
      have h2 : ((2 ^ (n + 1 + 1) : Nat) : Rat) = 2 * ((2 ^ (n + 1) : Nat) : Rat) := by
        push_cast [Nat.pow_succ]; grind
      rw [h2, Rat.inv_mul_rev, ← Rat.mul_assoc, Rat.mul_comm 2, Rat.mul_assoc,
        Rat.mul_inv_cancel 2 (by decide), Rat.mul_one]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [show (n : Int) + 1 = ((n + 1 : Nat) : Int) by omega, pow2_natCast, pow2_natCast]
    push_cast [Nat.pow_succ]
    grind

private theorem pow2_add_nat (a : Int) (n : Nat) : pow2 (a + n) = pow2 a * pow2 n := by
  induction n with
  | zero => simp [pow2]
  | succ n ih =>
    rw [show a + ((n + 1 : Nat) : Int) = (a + n) + 1 by omega, pow2_succ, ih,
      show ((n + 1 : Nat) : Int) = (n : Int) + 1 by omega, pow2_succ]
    grind

private theorem pow2_sub_nat (a : Int) (n : Nat) : pow2 (a - n) = pow2 a * pow2 (-(n : Int)) := by
  have h := pow2_add_nat (a - n) n
  rw [show a - n + n = a by omega] at h
  have h2 := pow2_add_nat (-(n : Int)) n
  rw [show -(n : Int) + n = 0 by omega, pow2_zero] at h2
  rw [h, Rat.mul_assoc, Rat.mul_comm (pow2 n), ← h2, Rat.mul_one]

theorem pow2_add (a b : Int) : pow2 (a + b) = pow2 a * pow2 b := by
  rcases Int.lt_or_le b 0 with hb | hb
  · obtain ⟨n, hn⟩ : ∃ n : Nat, b = -(n : Int) := ⟨(-b).toNat, by omega⟩
    subst hn
    rw [show a + -(n : Int) = a - n by omega, pow2_sub_nat]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hb
    exact pow2_add_nat a n

theorem pow2_mul_pow2_neg (k : Int) : pow2 k * pow2 (-k) = 1 := by
  rw [← pow2_add, show k + -k = 0 by omega, pow2_zero]

theorem pow2_lt {a b : Int} (h : a < b) : pow2 a < pow2 b := by
  obtain ⟨n, hn⟩ : ∃ n : Nat, b = a + ((n + 1 : Nat) : Int) := ⟨(b - a - 1).toNat, by omega⟩
  subst hn
  rw [pow2_add, pow2_natCast]
  have h1 : (1 : Rat) < ((2 ^ (n + 1) : Nat) : Rat) := by
    have : 1 < 2 ^ (n + 1) := Nat.one_lt_two_pow (by omega)
    exact_mod_cast this
  have := (Rat.mul_lt_mul_left (pow2_pos a)).mpr h1
  rwa [Rat.mul_one] at this

theorem pow2_le {a b : Int} (h : a ≤ b) : pow2 a ≤ pow2 b := by
  rcases Int.lt_or_le a b with h' | h'
  · exact Rat.le_of_lt (pow2_lt h')
  · rw [show a = b by omega]; exact Rat.le_refl

theorem pow2_lt_pow2_iff {a b : Int} : pow2 a < pow2 b ↔ a < b := by
  refine ⟨fun h => ?_, pow2_lt⟩
  rcases Int.lt_or_le a b with h' | h'
  · exact h'
  · exact absurd h (Rat.not_lt.mpr (pow2_le h'))

private theorem cross_lt {X Y Z W : Rat} (hY : 0 < Y) (hW : 0 < W) (h : X * W < Z * Y) :
    X * Y⁻¹ < Z * W⁻¹ := by
  have hp : 0 < Y⁻¹ * W⁻¹ := by
    have := (Rat.mul_lt_mul_left (Rat.inv_pos.mpr hY)).mpr (Rat.inv_pos.mpr hW)
    rwa [Rat.mul_zero] at this
  have hY0 : Y ≠ 0 := (Rat.ne_of_lt hY).symm
  have hW0 : W ≠ 0 := (Rat.ne_of_lt hW).symm
  have e1 : X * Y⁻¹ = (X * W) * (Y⁻¹ * W⁻¹) := by
    rw [Rat.mul_comm Y⁻¹, ← Rat.mul_assoc, Rat.mul_assoc X, Rat.mul_inv_cancel W hW0, Rat.mul_one]
  have e2 : Z * W⁻¹ = (Z * Y) * (Y⁻¹ * W⁻¹) := by
    rw [← Rat.mul_assoc, Rat.mul_assoc Z, Rat.mul_inv_cancel Y hY0, Rat.mul_one]
  rw [e1, e2]
  exact Rat.mul_lt_mul_of_pos_right h hp

private theorem natCast_pos {n : Nat} (h : 0 < n) : (0 : Rat) < (n : Rat) := by exact_mod_cast h

/-- `floorLog2 a` is the `e` with `2 ^ e ≤ a < 2 ^ (e + 1)`. -/
theorem floorLog2_eq {a : Rat} {e : Int} (h1 : pow2 e ≤ a) (h2 : a < pow2 (e + 1)) :
    floorLog2 a = e := by
  have ha : 0 < a := by have := pow2_pos e; grind
  have hnum : 0 < a.num := by
    have := (Rat.lt_iff 0 a).mp ha
    simpa using this
  generalize hn : a.num.toNat = n
  generalize hd : a.den = d
  have hn0 : n ≠ 0 := by omega
  have hd0 : d ≠ 0 := by rw [← hd]; exact a.den_nz
  have hadef : a = (n : Rat) * (d : Rat)⁻¹ := by
    rw [← Rat.div_def]
    have := Rat.num_divInt_den a
    rw [Rat.divInt_eq_div] at this
    have hnn : (a.num : Rat) = ((n : Int) : Rat) := by rw [← hn, Int.toNat_of_nonneg (by omega)]
    rw [hnn, hd] at this
    rw [← this]
    norm_cast
  generalize hi : n.log2 = i
  generalize hj : d.log2 = j
  have hi1 : 2 ^ i ≤ n := hi ▸ Nat.log2_self_le hn0
  have hi2 : n < 2 ^ (i + 1) := hi ▸ Nat.lt_log2_self
  have hj1 : 2 ^ j ≤ d := hj ▸ Nat.log2_self_le hd0
  have hj2 : d < 2 ^ (j + 1) := hj ▸ Nat.lt_log2_self
  have hlow : pow2 ((i : Int) - j - 1) < a := by
    rw [show (i : Int) - j - 1 = (i : Int) + -((j : Int) + 1) by omega, pow2_add, pow2_natCast,
      pow2_neg_succ, hadef]
    apply cross_lt (natCast_pos (Nat.two_pow_pos _)) (natCast_pos (by omega))
    have : 2 ^ i * d < n * 2 ^ (j + 1) :=
      Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hj2 (Nat.two_pow_pos _))
        (Nat.mul_le_mul_right _ hi1)
    exact_mod_cast this
  have hhigh : a < pow2 ((i : Int) - j + 1) := by
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · rw [hj0, show (i : Int) - ((0 : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) by omega,
        pow2_natCast, hadef]
      have hd1 : d = 1 := by have := hj2; rw [hj0] at this; omega
      rw [hd1]
      have : (n : Rat) < ((2 ^ (i + 1) : Nat) : Rat) := by exact_mod_cast hi2
      rw [show ((1 : Nat) : Rat)⁻¹ = 1 by decide +kernel, Rat.mul_one]
      exact this
    · obtain ⟨j', hj'⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [show (i : Int) - j + 1 = ((i + 1 : Nat) : Int) + -((j' : Int) + 1) by omega, pow2_add,
        pow2_natCast, pow2_neg_succ, hadef, ← hj']
      apply cross_lt (natCast_pos (by omega)) (natCast_pos (Nat.two_pow_pos _))
      have : n * 2 ^ j < 2 ^ (i + 1) * d :=
        Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hi2 (Nat.two_pow_pos _))
          (Nat.mul_le_mul_left _ hj1)
      exact_mod_cast this
  unfold floorLog2
  simp only
  rw [hn, hd, hi, hj]
  split
  · have := pow2_lt_pow2_iff.mp (show pow2 e < pow2 ((i : Int) - j + 1) by grind)
    have := pow2_lt_pow2_iff.mp (show pow2 ((i : Int) - j) < pow2 (e + 1) by grind)
    omega
  · rename_i hc
    have hc' := Rat.not_le.mp hc
    have := pow2_lt_pow2_iff.mp (show pow2 e < pow2 ((i : Int) - j) by grind)
    have := pow2_lt_pow2_iff.mp (show pow2 ((i : Int) - j - 1) < pow2 (e + 1) by grind)
    omega

/-- `floorLog2` of an integer significand with `p` bits (`2 ^ (p-1) ≤ N < 2 ^ p`) scaled by
`2 ^ k`. -/
theorem floorLog2_natCast_mul_pow2 (N p : Nat) (k : Int) (h1 : 2 ^ p ≤ N) (h2 : N < 2 ^ (p + 1)) :
    floorLog2 ((N : Rat) * pow2 k) = p + k := by
  apply floorLog2_eq
  · rw [pow2_add, pow2_natCast]
    apply Rat.mul_le_mul_of_nonneg_right _ (Rat.le_of_lt (pow2_pos k))
    exact_mod_cast h1
  · rw [show (p : Int) + k + 1 = ((p + 1 : Nat) : Int) + k by omega, pow2_add, pow2_natCast]
    apply Rat.mul_lt_mul_of_pos_right _ (pow2_pos k)
    exact_mod_cast h2

private theorem floor_natCast (n : Nat) : (n : Rat).floor = n := by
  rw [Rat.floor_def]; simp

/-- Rounding an integer to the nearest integer leaves it. -/
theorem roundHalfEven_natCast (n : Nat) : roundHalfEven (n : Rat) = n := by
  unfold roundHalfEven
  simp only [floor_natCast]
  rw [if_pos (Or.inl (by
    have : ((n : Int) : Rat) = (n : Rat) := by norm_cast
    rw [this, Rat.sub_self]; decide +kernel))]
  simp

namespace binary64

private theorem t_eq : binary64.t = 52 := rfl
private theorem w_eq : binary64.w = 11 := rfl
private theorem bias_eq : binary64.bias = 1023 := by decide +kernel
private theorem emax_eq : binary64.emax = 1023 := by decide +kernel
private theorem emin_eq : binary64.emin = -1022 := by decide +kernel

/-- The bits of a packed `float64`: sign, biased exponent `E < 2 ^ 11`, trailing significand
`T < 2 ^ 52`. -/
theorem pack_toNat (s : Bool) (E T : Nat) (hE : E < 2 ^ 11) (hT : T < 2 ^ 52) :
    (binary64.pack s E T).toNat = s.toNat * 2 ^ 63 + E * 2 ^ 52 + T := by
  change (BitVec.ofBool s ++ BitVec.ofNat 11 E ++ BitVec.ofNat 52 T).toNat = _
  rw [BitVec.toNat_append, BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hE, Nat.mod_eq_of_lt hT, ← Nat.shiftLeft_add_eq_or_of_lt hT,
    ← Nat.shiftLeft_add_eq_or_of_lt hE, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  cases s <;> simp [Nat.add_mul] <;> omega

/-- A `float64`'s bits: sign bit, biased exponent `E`, trailing significand `T`. -/
theorem toNat_fields (x : w64) :
    x.toNat = x.msb.toNat * 2 ^ 63 + (x.toNat / 2 ^ 52 % 2 ^ 11) * 2 ^ 52 + x.toNat % 2 ^ 52 := by
  have hx := x.isLt
  cases hm : x.msb
  · have := (BitVec.msb_eq_false_iff_two_mul_lt).mp hm
    simp only [Bool.toNat_false]
    omega
  · have := (BitVec.msb_eq_true_iff_two_mul_ge).mp hm
    simp only [Bool.toNat_true]
    omega

/-- The value of a normal `float64` (biased exponent `E` in `[1, 2046]`, trailing significand
`T`): `±(2 ^ 52 + T) * 2 ^ (E - 1075)`. -/
theorem decode_normal (x : w64) (E T : Nat) (hE : x.toNat / 2 ^ 52 % 2 ^ 11 = E)
    (hT : x.toNat % 2 ^ 52 = T) (hE1 : 1 ≤ E) (hE2 : E ≤ 2046) :
    binary64.decode x = .finite x.msb (((2 ^ 52 + T : Nat) : Rat) * pow2 ((E : Int) - 1075)) := by
  unfold Format.decode
  simp only [t_eq, w_eq, bias_eq, hE, hT]
  rw [if_neg (by omega), if_neg (by omega), Lean.Grind.Semiring.natCast_add,
    Lean.Grind.Semiring.natCast_pow,
    show (E : Int) - 1023 - ((52 : Nat) : Int) = (E : Int) - 1075 by omega]
  rfl

theorem decode_two : binary64.decode (W64 0x4000000000000000) = .finite false 2 := by
  decide +kernel

end binary64

end ieee754

/-- **Doubling is exact on normal `float64`s.** `x * 2.0`, of a normal `x` (of either sign) whose
biased exponent is below the largest finite one (so that the product is normal too), is `x`'s
bits plus `2 ^ 52`: the biased exponent plus one, the sign and the significand unchanged. -/
theorem float64Mul_two_normal (x f : w64) (hE1 : 1 ≤ x.toNat / 2 ^ 52 % 2 ^ 11)
    (hE2 : x.toNat / 2 ^ 52 % 2 ^ 11 < 2046)
    (hf : float64Encodes (float64Mul x (W64 0x4000000000000000)) f) :
    f.toNat = x.toNat + 2 ^ 52 := by
  generalize hE : x.toNat / 2 ^ 52 % 2 ^ 11 = E at hE1 hE2
  generalize hT : x.toNat % 2 ^ 52 = T
  have hxf := binary64.toNat_fields x
  rw [hE, hT] at hxf
  have hT' : T < 2 ^ 52 := by omega
  generalize hN : 2 ^ 52 + T = N
  have hN1 : 2 ^ 52 ≤ N := by omega
  have hN2 : N < 2 ^ (52 + 1) := by omega
  have hfl : ∀ k : Int, floorLog2 ((N : Rat) * pow2 k) = 52 + k := fun k =>
    floorLog2_natCast_mul_pow2 N 52 k hN1 hN2
  have hmax : max (52 + ((E : Int) - 1074)) (-1022) = 52 + ((E : Int) - 1074) := by omega
  have hr : (N : Rat) * pow2 ((E : Int) - 1074) * pow2 (((52 : Nat) : Int) - (52 + ((E : Int) - 1074))) =
      (N : Rat) := by
    rw [Rat.mul_assoc, ← pow2_add,
      show (E : Int) - 1074 + (((52 : Nat) : Int) - (52 + ((E : Int) - 1074))) = 0 by omega,
      pow2_zero, Rat.mul_one]
  have hm : float64Mul x (W64 0x4000000000000000) =
      .finite x.msb ((N : Rat) * pow2 ((E : Int) - 1074)) := by
    simp only [float64Mul, Format.mul_unseal, Format.mulDef]
    rw [binary64.decode_normal x E T hE hT hE1 (by omega), binary64.decode_two]
    simp only [Bool.xor_false]
    rw [hN, Rat.mul_assoc, Rat.mul_comm (pow2 _), ← pow2_succ,
      show (E : Int) - 1075 + 1 = (E : Int) - 1074 by omega]
    unfold Format.round
    simp only [binary64.t_eq, binary64.emin_eq, binary64.emax_eq, hfl]
    have he : 52 + ((E : Int) - 1074) - ((52 : Nat) : Int) = (E : Int) - 1074 := by omega
    simp only [hmax, hr, roundHalfEven_natCast, he]
    have hp := pow2_pos ((E : Int) - 1074)
    have hlt : (N : Rat) * pow2 ((E : Int) - 1074) < pow2 (1023 + 1) := by
      rw [show (1023 + 1 : Int) = ((53 : Nat) : Int) + (((E : Int) - 1074) + (971 - ((E : Int) - 1074))) by omega,
        pow2_add, pow2_add, ← Rat.mul_assoc, pow2_natCast]
      have hq : 1 ≤ pow2 (971 - ((E : Int) - 1074)) := by
        have := pow2_le (show (0 : Int) ≤ 971 - ((E : Int) - 1074) by omega)
        rwa [pow2_zero] at this
      have hN' : (N : Rat) < ((2 ^ 53 : Nat) : Rat) := by exact_mod_cast hN2
      have := Rat.mul_lt_mul_of_pos_right hN' hp
      have h0 : 0 ≤ ((2 ^ 53 : Nat) : Rat) * pow2 ((E : Int) - 1074) :=
        Rat.le_of_lt (Rat.mul_pos (by decide +kernel) hp)
      have h3 := Rat.mul_le_mul_of_nonneg_left hq h0
      rw [Rat.mul_one] at h3
      grind
    rw [if_pos hlt]
  rw [hm] at hf
  simp only [float64Encodes, Format.encodes, Format.encode] at hf
  simp only [binary64.t_eq, binary64.emin_eq, binary64.bias_eq, hfl] at hf
  simp only [hmax, hr, floor_natCast, Int.toNat_natCast] at hf
  rw [if_neg (by omega)] at hf
  simp only at hf
  subst hf
  rw [show (52 + ((E : Int) - 1074) + 1023).toNat = E + 1 by omega, show N - 2 ^ 52 = T by omega]
  rw [show x.toNat + 2 ^ 52 = x.msb.toNat * 2 ^ 63 + (E + 1) * 2 ^ 52 + T by omega]
  exact binary64.pack_toNat _ _ _ (by omega) hT'

/-- `float64Mul_two_normal` for a positive `x`, its bits as a range: from the smallest positive
normal (`2 ^ 52`, `0x0010000000000000`) to the largest whose double is finite. -/
theorem float64Mul_two_pos_normal (x f : w64) (h1 : 2 ^ 52 ≤ x.toNat)
    (h2 : x.toNat + 2 ^ 52 < 0x7FF0000000000000)
    (hf : float64Encodes (float64Mul x (W64 0x4000000000000000)) f) :
    f.toNat = x.toNat + 2 ^ 52 :=
  float64Mul_two_normal x f (by omega) (by omega) hf

/-- A positive finite `float64` (a clear sign bit, not zero, below `+∞`) is not `≤ 0`. -/
theorem float64Leb_zero_false_of_pos (x : w64) (h1 : 0 < x.toNat)
    (h2 : x.toNat < 0x7FF0000000000000) : float64Leb x (W64 0) = false := by
  have hmsb : x.msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt]; omega
  have hpos : ∃ m, 0 < m ∧ binary64.decode x = .finite false m := by
    unfold Format.decode
    simp only [hmsb, binary64.t_eq, binary64.w_eq]
    rw [if_neg (by omega)]
    split
    · refine ⟨_, ?_, rfl⟩
      exact Rat.mul_pos (natCast_pos (by omega)) (pow2_pos _)
    · refine ⟨_, ?_, rfl⟩
      exact Rat.mul_pos (by exact_mod_cast (show (0 : Nat) < 2 ^ 52 + x.toNat % 2 ^ 52 by omega))
        (pow2_pos _)
  obtain ⟨m, hm, hd⟩ := hpos
  simp only [float64Leb, Format.leb_unseal, Format.lebDef, hd, decode_zero64, signed]
  simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_false_iff_not, Rat.not_le]
  exact hm

open Perennial.go in
/-- `x < 0` of a `float64` `x` with a clear sign bit is `false`: the step of `x < 0`
(`go.lt_float64`) with `#false` for `#(float64Leb x 0 && !float64Eq x 0)`. -/
theorem lt_float64_zero_step_of_sign_clear [GooseExts] [GoLocalContext] [GoGlobalContext]
    [GoSemanticsFunctions]
    [go.Float64Semantics] (x : w64) (h : 0 ≤ sint.Z x) :
    ⟦GoOp GoLt go.float64, (#x, #(W64 0))⟧ ⤳[under] #false := by
  have := go.lt_float64 x (W64 0)
  rwa [lt_zero_false_of_sign_clear x h] at this

section wp
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]
variable {s : Stuckness} {E : CoPset}

/-- A Go instruction whose pure step is a relation: `op` applied to `arg` steps to any
`#(inj f)` with `P f` (and some `f` satisfies `P`). The float arithmetic rules have this
form (`go.plus_float64`, ...). -/
theorem wp_go_step_rel {V : Type} (inj : V → val) (op : GoInstruction) (arg : val)
    (P : V → Prop)
    (hop : ∀ e gs gs', IsGoStep op arg e gs gs' ↔ is_go_step_pure op arg e ∧ gs = gs')
    (hstep : is_go_step_pure op arg = fun e => ∃ f, e = Val (inj f) ∧ P f)
    (hP : ∃ f, P f) (Harg : arg.isPanic = false := by simp) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction op)) (Val arg)) @ s; E
    {{ (f : V), RET inj f; ⌜P f⌝ }} := by
  iintro %Φ _ HΦ
  obtain ⟨f0, hf0⟩ := hP
  iapply wp_GoInstruction' (s := s) (E := E) op arg Φ
    (fun gs => ⟨Val (inj f0), gs, (hop _ _ _).mpr ⟨by rw [hstep]; exact ⟨f0, rfl, hf0⟩, rfl⟩⟩)
    Harg
  inext
  iintro %e' %gs %gs' %Hstep _ Hctx
  obtain ⟨Hp, rfl⟩ := (hop _ _ _).mp Hstep
  rw [hstep] at Hp
  obtain ⟨f, rfl, Hf⟩ := Hp
  imodintro
  iframe Hctx
  iapply wp_value'
  iapply HΦ
  ipureintro; exact Hf

/-! The arithmetic operations of `float64` and `float32` (and of the named types whose
underlying type they are): the result `f` encodes IEEE 754's result value (`float64Encodes`:
its bit pattern, or any NaN if it is NaN). Use as `wp_apply wp_float64_add as %f Hf`. -/

theorem wp_float64_add {t : go.GoType} [t ↓u go.float64] (v1 v2 : w64) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoOp GoPlus t))) (Val glv((#v1, #v2)))) @ s; E
    {{ (f : w64), RET #f; ⌜float64Encodes (float64Add v1 v2) f⌝ }} :=
  wp_go_step_rel (fun f : w64 => #f) _ _ _ (fun _ _ _ => Iff.rfl) (go.plus_float64 v1 v2)
    (float64Encodes_exists _)

theorem wp_float64_sub {t : go.GoType} [t ↓u go.float64] (v1 v2 : w64) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoOp GoSub t))) (Val glv((#v1, #v2)))) @ s; E
    {{ (f : w64), RET #f; ⌜float64Encodes (float64Sub v1 v2) f⌝ }} :=
  wp_go_step_rel (fun f : w64 => #f) _ _ _ (fun _ _ _ => Iff.rfl) (go.sub_float64 v1 v2)
    (float64Encodes_exists _)

theorem wp_float64_mul {t : go.GoType} [t ↓u go.float64] (v1 v2 : w64) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoOp GoMul t))) (Val glv((#v1, #v2)))) @ s; E
    {{ (f : w64), RET #f; ⌜float64Encodes (float64Mul v1 v2) f⌝ }} :=
  wp_go_step_rel (fun f : w64 => #f) _ _ _ (fun _ _ _ => Iff.rfl) (go.mul_float64 v1 v2)
    (float64Encodes_exists _)

theorem wp_float64_div {t : go.GoType} [t ↓u go.float64] (v1 v2 : w64) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoOp GoDiv t))) (Val glv((#v1, #v2)))) @ s; E
    {{ (f : w64), RET #f; ⌜float64Encodes (float64Div v1 v2) f⌝ }} :=
  wp_go_step_rel (fun f : w64 => #f) _ _ _ (fun _ _ _ => Iff.rfl) (go.div_float64 v1 v2)
    (float64Encodes_exists _)

theorem wp_float64_neg {t : go.GoType} [t ↓u go.float64] (v : w64) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoUnOp GoNeg t))) (Val #v)) @ s; E
    {{ (f : w64), RET #f; ⌜float64Encodes (float64Neg v) f⌝ }} :=
  wp_go_step_rel (fun f : w64 => #f) _ _ _ (fun _ _ _ => Iff.rfl) (go.neg_float64 v)
    (float64Encodes_exists _)

theorem wp_float32_add {t : go.GoType} [t ↓u go.float32] (v1 v2 : w32) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoOp GoPlus t))) (Val glv((#v1, #v2)))) @ s; E
    {{ (f : w32), RET #f; ⌜float32Encodes (float32Add v1 v2) f⌝ }} :=
  wp_go_step_rel (fun f : w32 => #f) _ _ _ (fun _ _ _ => Iff.rfl) (go.plus_float32 v1 v2)
    (float32Encodes_exists _)

theorem wp_float32_sub {t : go.GoType} [t ↓u go.float32] (v1 v2 : w32) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoOp GoSub t))) (Val glv((#v1, #v2)))) @ s; E
    {{ (f : w32), RET #f; ⌜float32Encodes (float32Sub v1 v2) f⌝ }} :=
  wp_go_step_rel (fun f : w32 => #f) _ _ _ (fun _ _ _ => Iff.rfl) (go.sub_float32 v1 v2)
    (float32Encodes_exists _)

theorem wp_float32_mul {t : go.GoType} [t ↓u go.float32] (v1 v2 : w32) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoOp GoMul t))) (Val glv((#v1, #v2)))) @ s; E
    {{ (f : w32), RET #f; ⌜float32Encodes (float32Mul v1 v2) f⌝ }} :=
  wp_go_step_rel (fun f : w32 => #f) _ _ _ (fun _ _ _ => Iff.rfl) (go.mul_float32 v1 v2)
    (float32Encodes_exists _)

theorem wp_float32_div {t : go.GoType} [t ↓u go.float32] (v1 v2 : w32) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoOp GoDiv t))) (Val glv((#v1, #v2)))) @ s; E
    {{ (f : w32), RET #f; ⌜float32Encodes (float32Div v1 v2) f⌝ }} :=
  wp_go_step_rel (fun f : w32 => #f) _ _ _ (fun _ _ _ => Iff.rfl) (go.div_float32 v1 v2)
    (float32Encodes_exists _)

theorem wp_float32_neg {t : go.GoType} [t ↓u go.float32] (v : w32) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoUnOp GoNeg t))) (Val #v)) @ s; E
    {{ (f : w32), RET #f; ⌜float32Encodes (float32Neg v) f⌝ }} :=
  wp_go_step_rel (fun f : w32 => #f) _ _ _ (fun _ _ _ => Iff.rfl) (go.neg_float32 v)
    (float32Encodes_exists _)

/-! The conversions between `float64` and `float32` (`float32(x)`, `float64(x)`, also of named
types): the result `f` encodes the rounding of `x` (any NaN if `x` is NaN). -/

theorem wp_float64_to_float32 {t1 t2 : go.GoType} [t1 ↓u go.float64] [t2 ↓u go.float32]
    (v : w64) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (Convert t1 t2))) (Val #v)) @ s; E
    {{ (f : w32), RET #f; ⌜float32Encodes (float64ToFloat32 v) f⌝ }} :=
  wp_go_step_rel (fun f : w32 => #f) _ _ _ (fun _ _ _ => Iff.rfl)
    (go.convert_float64_to_float32 v) (float32Encodes_exists _)

theorem wp_float32_to_float64 {t1 t2 : go.GoType} [t1 ↓u go.float32] [t2 ↓u go.float64]
    (v : w32) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (Convert t1 t2))) (Val #v)) @ s; E
    {{ (f : w64), RET #f; ⌜float64Encodes (float32ToFloat64 v) f⌝ }} :=
  wp_go_step_rel (fun f : w64 => #f) _ _ _ (fun _ _ _ => Iff.rfl)
    (go.convert_float32_to_float64 v) (float64Encodes_exists _)

end wp

end Perennial
