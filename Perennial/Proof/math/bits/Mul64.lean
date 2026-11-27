/-
The proof of `math.bits.Mul64`.
-/
module

public import Perennial.Spec.math.bits.Mul64

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

/-- The schoolbook product on 32-bit halves that `Mul64` computes: its high word is the high
half of the product, and no intermediate sum overflows 64 bits. -/
theorem math.bits.mul64_nat (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    (a / 2^32) * (b / 2^32) + ((a / 2^32) * (b % 2^32) + (a % 2^32) * (b % 2^32) / 2^32) / 2^32 +
      (((a / 2^32) * (b % 2^32) + (a % 2^32) * (b % 2^32) / 2^32) % 2^32 +
        (a % 2^32) * (b / 2^32)) / 2^32 = a * b / 2^64 ∧
    (a % 2^32) * (b % 2^32) < 2^64 ∧
    (a / 2^32) * (b % 2^32) + (a % 2^32) * (b % 2^32) / 2^32 < 2^64 ∧
    ((a / 2^32) * (b % 2^32) + (a % 2^32) * (b % 2^32) / 2^32) % 2^32 + (a % 2^32) * (b / 2^32) < 2^64 ∧
    (a / 2^32) * (b / 2^32) < 2^64 ∧
    (a / 2^32) * (b / 2^32) + ((a / 2^32) * (b % 2^32) + (a % 2^32) * (b % 2^32) / 2^32) / 2^32 < 2^64 ∧
    a * b / 2^64 < 2^64 := by
  have ha0 : a % 2^32 < 2^32 := Nat.mod_lt _ (Nat.two_pow_pos 32)
  have hb0 : b % 2^32 < 2^32 := Nat.mod_lt _ (Nat.two_pow_pos 32)
  have ha1 : a / 2^32 < 2^32 := by omega
  have hb1 : b / 2^32 < 2^32 := by omega
  have hab : a * b = ((a / 2^32) * (b / 2^32)) * 2^64 +
      ((a / 2^32) * (b % 2^32) + (a % 2^32) * (b / 2^32)) * 2^32 + (a % 2^32) * (b % 2^32) := by
    conv => lhs; rw [← Nat.div_add_mod a (2^32), ← Nat.div_add_mod b (2^32)]
    grind
  have hP : (a / 2^32) * (b / 2^32) ≤ (2^32-1)*(2^32-1) := Nat.mul_le_mul (by omega) (by omega)
  have hQ : (a / 2^32) * (b % 2^32) ≤ (2^32-1)*(2^32-1) := Nat.mul_le_mul (by omega) (by omega)
  have hR : (a % 2^32) * (b / 2^32) ≤ (2^32-1)*(2^32-1) := Nat.mul_le_mul (by omega) (by omega)
  have hS : (a % 2^32) * (b % 2^32) ≤ (2^32-1)*(2^32-1) := Nat.mul_le_mul (by omega) (by omega)
  generalize (a / 2^32) * (b / 2^32) = P at *
  generalize (a / 2^32) * (b % 2^32) = Q at *
  generalize (a % 2^32) * (b / 2^32) = R at *
  generalize (a % 2^32) * (b % 2^32) = S at *
  generalize a * b = AB at *
  omega

/-- `Mul64`'s high word, as the translation computes it, is the high half of the product. -/
theorem math.bits.mul64_hi (x y : w64) :
    x >>> W64 32 * y >>> W64 32 +
            (x >>> W64 32 * (y &&& W64 4294967295) + ((x &&& W64 4294967295) * (y &&& W64 4294967295)) >>> W64 32) >>>
              W64 32 +
          ((x >>> W64 32 * (y &&& W64 4294967295) + ((x &&& W64 4294967295) * (y &&& W64 4294967295)) >>> W64 32 &&&
                W64 4294967295) +
              (x &&& W64 4294967295) * y >>> W64 32) >>>
            W64 32 = W64 (uint.Z x * uint.Z y / 2 ^ 64) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := math.bits.mul64_nat x.toNat y.toNat x.isLt y.isLt
  apply BitVec.eq_of_toNat_eq
  have hm : ∀ z : w64, (z &&& W64 4294967295).toNat = z.toNat % 2^32 := by
    intro z; rw [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 32
  have hs : ∀ z : w64, (z >>> W64 32).toNat = z.toNat / 2^32 := by
    intro z; simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hr : (W64 (uint.Z x * uint.Z y / 2 ^ 64)).toNat = x.toNat * y.toNat / 2 ^ 64 := by
    simp only [uint.Z, W64, BitVec.toNat_ofInt]
    rw [← Int.natCast_mul]
    generalize x.toNat * y.toNat = AB at *
    omega
  simp only [BitVec.toNat_add, BitVec.toNat_mul, hm, hs, hr]
  generalize BitVec.toNat x / 2^32 * (BitVec.toNat y / 2^32) = P at *
  generalize BitVec.toNat x / 2^32 * (BitVec.toNat y % 2^32) = Q at *
  generalize BitVec.toNat x % 2^32 * (BitVec.toNat y / 2^32) = R at *
  generalize BitVec.toNat x % 2^32 * (BitVec.toNat y % 2^32) = S at *
  generalize BitVec.toNat x * BitVec.toNat y = AB at *
  omega

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.bits.Assumptions]

theorem math.bits.Mul64.wp_proof : math.bits.Mul64.spec (GF := GF) (hG := hG) := by
  intro x y
  wp_start
  wp_auto
  rw [math.bits.mul64_hi]
  wp_end

end proof

end Perennial
