/-
Machine words. Words are `BitVec n`. `uint.Z w` is the unsigned value (an
`Int`), `sint.Z w` the signed value.
-/
import Std.Tactic.BVDecide

namespace Perennial

abbrev w64 := BitVec 64
abbrev w32 := BitVec 32
abbrev w16 := BitVec 16
abbrev w8 := BitVec 8
abbrev U64 := w64
abbrev U32 := w32
abbrev U16 := w16
abbrev U8 := w8
abbrev Byte := w8

/-- `W64 z` is `z mod 2^64` as a word. -/
abbrev W64 (z : Int) : w64 := BitVec.ofInt 64 z
abbrev W32 (z : Int) : w32 := BitVec.ofInt 32 z
abbrev W16 (z : Int) : w16 := BitVec.ofInt 16 z
abbrev W8 (z : Int) : w8 := BitVec.ofInt 8 z

namespace uint
/-- Unsigned interpretation. -/
abbrev Z {n : Nat} (w : BitVec n) : Int := (w.toNat : Int)
/-- Unsigned interpretation as a `Nat`. -/
abbrev nat {n : Nat} (w : BitVec n) : Nat := w.toNat
end uint

namespace sint
/-- Signed (two's complement) interpretation. -/
abbrev Z {n : Nat} (w : BitVec n) : Int := w.toInt
abbrev nat {n : Nat} (w : BitVec n) : Nat := w.toInt.toNat
end sint

theorem uint_Z_nonneg {n} (w : BitVec n) : 0 ≤ uint.Z w := by simp [uint.Z]

theorem uint_Z_lt {n} (w : BitVec n) : uint.Z w < 2 ^ n := by
  simp only [uint.Z]; exact_mod_cast w.isLt

theorem uint_Z_W64 (z : Int) (h0 : 0 ≤ z) (h1 : z < 2 ^ 64) : uint.Z (W64 z) = z := by
  simp only [uint.Z, W64, BitVec.toNat_ofInt]; omega

theorem uint_Z_W32 (z : Int) (h0 : 0 ≤ z) (h1 : z < 2 ^ 32) : uint.Z (W32 z) = z := by
  simp only [uint.Z, W32, BitVec.toNat_ofInt]; omega

theorem uint_Z_W16 (z : Int) (h0 : 0 ≤ z) (h1 : z < 2 ^ 16) : uint.Z (W16 z) = z := by
  simp only [uint.Z, W16, BitVec.toNat_ofInt]; omega

theorem uint_Z_W8 (z : Int) (h0 : 0 ≤ z) (h1 : z < 2 ^ 8) : uint.Z (W8 z) = z := by
  simp only [uint.Z, W8, BitVec.toNat_ofInt]; omega

theorem uint_Z_inj {n} {x y : BitVec n} : uint.Z x = uint.Z y ↔ x = y := by
  simp only [uint.Z]; constructor
  · intro h; apply BitVec.eq_of_toNat_eq; omega
  · rintro rfl; rfl

end Perennial
