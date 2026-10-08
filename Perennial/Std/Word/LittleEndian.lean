/-
Little-endian encodings of `w64` and `w32`.

These are plain (unsealed) definitions, with `_def`/`_unseal` lemmas so that
`rw [u64Le_unseal]` works.
-/
module

public import Perennial.Std.LittleEndian
public import Perennial.Std.ListLen

@[expose] public section

namespace Perennial

def u64LeDef (x : U64) : List Byte := LittleEndian.split 8 x.toNat
def u64Le (x : U64) : List Byte := u64LeDef x
theorem u64Le_unseal : @u64Le = @u64LeDef := rfl

def u32LeDef (x : U32) : List Byte := LittleEndian.split 4 x.toNat
def u32Le (x : U32) : List Byte := u32LeDef x
theorem u32Le_unseal : @u32Le = @u32LeDef := rfl

def leToU64Def (l : List Byte) : U64 := BitVec.ofNat 64 (LittleEndian.combine l)
def leToU64 (l : List Byte) : U64 := leToU64Def l
theorem leToU64_unseal : @leToU64 = @leToU64Def := rfl

def leToU32Def (l : List Byte) : U32 := BitVec.ofNat 32 (LittleEndian.combine l)
def leToU32 (l : List Byte) : U32 := leToU32Def l
theorem leToU32_unseal : @leToU32 = @leToU32Def := rfl

/-! ### 64-bit -/

theorem u64Le_0 : u64Le (W64 0) = List.replicate 8 (W8 0) := by decide

@[len] theorem u64Le_length (x : U64) : (u64Le x).length = 8 := LittleEndian.length_split _ _

theorem u64Le_to_word (x : U64) : leToU64 (u64Le x) = x := by
  simp only [leToU64, leToU64Def, u64Le, u64LeDef, LittleEndian.combine_split]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have := x.isLt; omega

theorem leToU64_le (bs : List Byte) (h : bs.length = 8) : u64Le (leToU64 bs) = bs := by
  simp only [leToU64, leToU64Def, u64Le, u64LeDef, BitVec.toNat_ofNat]
  have := LittleEndian.combine_bound bs
  rw [h] at this
  rw [Nat.mod_eq_of_lt this]
  exact LittleEndian.split_combine 8 bs h

theorem u64Le_inj {x y : U64} (h : u64Le x = u64Le y) : x = y := by
  have := congrArg leToU64 h; rwa [u64Le_to_word, u64Le_to_word] at this

/-! ### 32-bit -/

theorem u32Le_0 : u32Le (W32 0) = List.replicate 4 (W8 0) := by decide

@[len] theorem u32Le_length (x : U32) : (u32Le x).length = 4 := LittleEndian.length_split _ _

theorem u32Le_to_word (x : U32) : leToU32 (u32Le x) = x := by
  simp only [leToU32, leToU32Def, u32Le, u32LeDef, LittleEndian.combine_split]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have := x.isLt; omega

theorem leToU32_le (bs : List Byte) (h : bs.length = 4) : u32Le (leToU32 bs) = bs := by
  simp only [leToU32, leToU32Def, u32Le, u32LeDef, BitVec.toNat_ofNat]
  have := LittleEndian.combine_bound bs
  rw [h] at this
  rw [Nat.mod_eq_of_lt this]
  exact LittleEndian.split_combine 4 bs h

theorem u32Le_inj {x y : U32} (h : u32Le x = u32Le y) : x = y := by
  have := congrArg leToU32 h; rwa [u32Le_to_word, u32Le_to_word] at this

theorem combine_bound (bs : List Byte) : LittleEndian.combine bs < 2 ^ (8 * bs.length) :=
  LittleEndian.combine_bound bs

theorem combine_unfold (b : Byte) (bs : List Byte) :
    LittleEndian.combine (b :: bs) = uint.nat b + 256 * LittleEndian.combine bs := rfl

end Perennial
