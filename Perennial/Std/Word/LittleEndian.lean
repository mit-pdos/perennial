/-
Port of `src/Helpers/Word/LittleEndian.v`: little-endian encodings of `w64`
and `w32`.

Rocq seals these definitions (`u64_le := sealed u64_le_def`); here they are
plain definitions with the same `_def`/`_unseal` names, so that
`rw [u64_le_unseal]` still works.
-/
import Perennial.Std.LittleEndian
import Perennial.Std.ListLen

namespace Perennial

def u64_le_def (x : u64) : List byte := LittleEndian.split 8 x.toNat
def u64_le (x : u64) : List byte := u64_le_def x
theorem u64_le_unseal : @u64_le = @u64_le_def := rfl

def u32_le_def (x : u32) : List byte := LittleEndian.split 4 x.toNat
def u32_le (x : u32) : List byte := u32_le_def x
theorem u32_le_unseal : @u32_le = @u32_le_def := rfl

def le_to_u64_def (l : List byte) : u64 := BitVec.ofNat 64 (LittleEndian.combine l)
def le_to_u64 (l : List byte) : u64 := le_to_u64_def l
theorem le_to_u64_unseal : @le_to_u64 = @le_to_u64_def := rfl

def le_to_u32_def (l : List byte) : u32 := BitVec.ofNat 32 (LittleEndian.combine l)
def le_to_u32 (l : List byte) : u32 := le_to_u32_def l
theorem le_to_u32_unseal : @le_to_u32 = @le_to_u32_def := rfl

/-! ### 64-bit -/

theorem u64_le_0 : u64_le (W64 0) = List.replicate 8 (W8 0) := by decide

@[len] theorem u64_le_length (x : u64) : (u64_le x).length = 8 := LittleEndian.length_split _ _

theorem u64_le_to_word (x : u64) : le_to_u64 (u64_le x) = x := by
  simp only [le_to_u64, le_to_u64_def, u64_le, u64_le_def, LittleEndian.combine_split]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have := x.isLt; omega

theorem le_to_u64_le (bs : List byte) (h : bs.length = 8) : u64_le (le_to_u64 bs) = bs := by
  simp only [le_to_u64, le_to_u64_def, u64_le, u64_le_def, BitVec.toNat_ofNat]
  have := LittleEndian.combine_bound bs
  rw [h] at this
  rw [Nat.mod_eq_of_lt this]
  exact LittleEndian.split_combine 8 bs h

theorem u64_le_inj {x y : u64} (h : u64_le x = u64_le y) : x = y := by
  have := congrArg le_to_u64 h; rwa [u64_le_to_word, u64_le_to_word] at this

/-! ### 32-bit -/

theorem u32_le_0 : u32_le (W32 0) = List.replicate 4 (W8 0) := by decide

@[len] theorem u32_le_length (x : u32) : (u32_le x).length = 4 := LittleEndian.length_split _ _

theorem u32_le_to_word (x : u32) : le_to_u32 (u32_le x) = x := by
  simp only [le_to_u32, le_to_u32_def, u32_le, u32_le_def, LittleEndian.combine_split]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have := x.isLt; omega

theorem le_to_u32_le (bs : List byte) (h : bs.length = 4) : u32_le (le_to_u32 bs) = bs := by
  simp only [le_to_u32, le_to_u32_def, u32_le, u32_le_def, BitVec.toNat_ofNat]
  have := LittleEndian.combine_bound bs
  rw [h] at this
  rw [Nat.mod_eq_of_lt this]
  exact LittleEndian.split_combine 4 bs h

theorem u32_le_inj {x y : u32} (h : u32_le x = u32_le y) : x = y := by
  have := congrArg le_to_u32 h; rwa [u32_le_to_word, u32_le_to_word] at this

theorem combine_bound (bs : List byte) : LittleEndian.combine bs < 2 ^ (8 * bs.length) :=
  LittleEndian.combine_bound bs

theorem combine_unfold (b : byte) (bs : List byte) :
    LittleEndian.combine (b :: bs) = uint.nat b + 256 * LittleEndian.combine bs := rfl

end Perennial
