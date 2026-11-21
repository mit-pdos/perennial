/-
Facts about the IEEE 754 float operations of the Go semantics
(`Perennial/Golang/Defn/Float.lean`): signs of conversions and comparisons with zero, and the
spec of `go.float64Result`/`go.float32Result` (an operation's result, any NaN if it is a NaN).
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

theorem msb_round (s : Bool) (m : Rat) : (f.round s m).msb = s := by
  unfold round
  dsimp only
  repeat' split
  all_goals exact f.msb_pack ..

theorem msb_roundRat_of_nonneg (q : Rat) (h : 0 ≤ q) : (f.roundRat q).msb = false := by
  have : ¬ q < 0 := fun h' => (Rat.not_le.mpr h') h
  simp [roundRat, this, msb_round]

theorem msb_ofInt_of_nonneg (n : Int) (h : 0 ≤ n) : (f.ofInt n).msb = false := by
  rw [ofInt_unseal, ofIntDef]
  exact f.msb_roundRat_of_nonneg _ (by exact_mod_cast h)

theorem pow2_nonneg (k : Int) : 0 ≤ pow2 k := by
  unfold pow2
  split
  · exact Rat.natCast_nonneg
  · exact Rat.le_of_lt (Rat.inv_pos.mpr (by
      have : (0 : Nat) < 2 ^ (-k).toNat := Nat.two_pow_pos _
      exact_mod_cast this))

/-- The data of a bit pattern with a clear sign bit: NaN, `+∞`, or a non-negative number. -/
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
  BitVec.toInt_nonneg_of_msb_false (binary64.msb_ofInt_of_nonneg _ h)
theorem uint64ToFloat64_sign_clear (n : w64) : 0 ≤ sint.Z (uint64ToFloat64 n) :=
  BitVec.toInt_nonneg_of_msb_false (binary64.msb_ofInt_of_nonneg _ (by omega))
theorem int32ToFloat64_sign_clear (n : w32) (h : 0 ≤ sint.Z n) : 0 ≤ sint.Z (int32ToFloat64 n) :=
  BitVec.toInt_nonneg_of_msb_false (binary64.msb_ofInt_of_nonneg _ h)
theorem uint32ToFloat64_sign_clear (n : w32) : 0 ≤ sint.Z (uint32ToFloat64 n) :=
  BitVec.toInt_nonneg_of_msb_false (binary64.msb_ofInt_of_nonneg _ (by omega))

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

theorem float64IsNaN_float64NaN : float64IsNaN float64NaN = true := by
  simp only [float64IsNaN, Format.isNaN_unseal, Format.isNaNDef]; decide
theorem float32IsNaN_float32NaN : float32IsNaN float32NaN = true := by
  simp only [float32IsNaN, Format.isNaN_unseal, Format.isNaNDef]; decide

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

/-- The result of a `float64` operation whose IEEE 754 result is `r`: `r`, or any NaN if `r`
is a NaN. -/
theorem wp_float64Result (r : w64) (Φ : val → IProp GF) :
    (∀ f : w64, ⌜f = r ∨ (float64IsNaN r = true ∧ float64IsNaN f = true)⌝ -∗ Φ #f) ⊢
      WP (go.float64Result r) @ s; E {{ Φ }} := by
  iintro HΦ
  rw [go.float64Result_unseal, go.float64ResultDef]
  cases hr : float64IsNaN r
  · simp only [Bool.false_eq_true, ↓reduceIte]
    wp_pures
    iapply HΦ
    ipureintro
    exact .inl rfl
  · simp only [↓reduceIte]
    wp_apply wp_ArbitraryInt as %x _
    rw [float64Eq_self]
    cases hx : float64IsNaN x
    · wp_pures
      iapply HΦ
      ipureintro
      simp [float64IsNaN_float64NaN]
    · wp_pures
      iapply HΦ
      ipureintro
      exact .inr ⟨trivial, hx⟩

/-- The result of a `float32` operation whose IEEE 754 result is `r`: `r`, or any NaN if `r`
is a NaN. -/
theorem wp_float32Result (r : w32) (Φ : val → IProp GF) :
    (∀ f : w32, ⌜f = r ∨ (float32IsNaN r = true ∧ float32IsNaN f = true)⌝ -∗ Φ #f) ⊢
      WP (go.float32Result r) @ s; E {{ Φ }} := by
  iintro HΦ
  rw [go.float32Result_unseal, go.float32ResultDef]
  cases hr : float32IsNaN r
  · simp only [Bool.false_eq_true, ↓reduceIte]
    wp_pures
    iapply HΦ
    ipureintro
    exact .inl rfl
  · simp only [↓reduceIte]
    wp_apply wp_ArbitraryInt as %x _
    rw [float32Eq_self]
    cases hx : float32IsNaN (W32 (uint.Z x))
    · wp_pures
      iapply HΦ
      ipureintro
      simp [float32IsNaN_float32NaN]
    · wp_pures
      iapply HΦ
      ipureintro
      exact .inr ⟨trivial, hx⟩


end wp

end Perennial
