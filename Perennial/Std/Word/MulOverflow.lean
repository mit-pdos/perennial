module

public import Perennial.Std.Word.Automation

@[expose] public section

noncomputable section

namespace Perennial

theorem mul_overflow_check_conservative (x y : w64) (h0 : 0 < uint.Z x)
    (h1 : (2 ^ 64 - 1) / uint.Z y ≥ uint.Z x) : uint.Z x * uint.Z y < 2 ^ 64 := by
  have hy := uint_Z_nonneg y
  have := Int.ediv_mul_le (2 ^ 64 - 1) (b := uint.Z y)
  by_cases hy0 : uint.Z y = 0
  · rw [hy0]; omega
  · have : uint.Z x * uint.Z y ≤ (2 ^ 64 - 1) / uint.Z y * uint.Z y :=
      Int.mul_le_mul_of_nonneg_right h1 hy
    have := Int.ediv_mul_le (2 ^ 64 - 1) hy0
    omega

theorem mul_overflow_check_correct (x y : w64) (hx : uint.Z x ≠ 0) (hy : uint.Z y ≠ 0) :
    2 ^ 64 - 1 < uint.Z x * uint.Z y ↔ (2 ^ 64 - 1) / uint.Z y < uint.Z x := by
  have hx0 := uint_Z_nonneg x
  have hy0 := uint_Z_nonneg y
  constructor
  · intro h
    apply Int.lt_of_not_ge; intro hc
    have := mul_overflow_check_conservative x y (by omega) (by omega)
    omega
  · intro h
    have h2 : (2 ^ 64 - 1) / uint.Z y + 1 ≤ uint.Z x := by omega
    have h3 := Int.mul_le_mul_of_nonneg_right h2 hy0
    have h4 := Int.lt_ediv_add_one_mul_self (2 ^ 64 - 1) (b := uint.Z y) (by omega)
    rw [Int.add_mul, Int.one_mul] at h3
    rw [Int.add_mul, Int.one_mul] at h4
    omega

end Perennial
