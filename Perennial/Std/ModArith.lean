/-
Overflow facts about `w64` addition.
-/
module

public import Perennial.Std.Word.Automation

@[expose] public section

namespace Perennial

theorem sum_overflow_check (x y : w64) :
    uint.Z (x + y) < uint.Z x ↔ uint.Z x + uint.Z y ≥ 2 ^ 64 := by word

theorem sum_nooverflow_l (x y : w64) (h : uint.Z x ≤ uint.Z (x + y)) :
    uint.Z (x + y) = uint.Z x + uint.Z y := by word

theorem word_add_comm (x y : w64) : x + y = y + x := by word

theorem sum_nooverflow_r (x y : w64) (h : uint.Z y ≤ uint.Z (x + y)) :
    uint.Z (x + y) = uint.Z x + uint.Z y := by word

theorem word_add1_neq (x : w64) : uint.Z x ≠ uint.Z (x + W64 1) := by word

end Perennial
