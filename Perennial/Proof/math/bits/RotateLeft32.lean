/-
The proof of `math.bits.RotateLeft32`.
-/
module

public import Perennial.Spec.math.bits.RotateLeft32

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace math.bits

/-- `x<<s | x>>(32-s)` is the rotation by `s`, for `s < 32` (`x >> 32` is `0`). -/
theorem rotl32_shifts (x : w32) (s : w64) (hs : s.toNat < 32) :
    (x <<< s ||| x >>> (W64 32 - s)) = x.rotateLeft s.toNat := by
  have h32 : (W64 32 - s).toNat = 32 - s.toNat := by
    rw [BitVec.toNat_sub]; simp; omega
  rw [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', h32, BitVec.rotateLeft_def,
    Nat.mod_eq_of_lt hs]

theorem and31_toNat (k : w64) : (k &&& W64 31).toNat = k.toNat % 32 := by
  rw [BitVec.toNat_and]
  show k.toNat &&& 31 = k.toNat % 32
  exact Nat.and_two_pow_sub_one_eq_mod k.toNat 5

end math.bits

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.bits.Assumptions]

theorem math.bits.RotateLeft32.wp_proof : math.bits.RotateLeft32.spec (GF := GF) (hG := hG) :=
    fun x k => by
  wp_start
  wp_auto
  have hs : (k &&& W64 31).toNat < 32 := by rw [math.bits.and31_toNat]; omega
  rw [math.bits.rotl32_shifts x _ hs, math.bits.and31_toNat]
  wp_end

end proof

end Perennial
