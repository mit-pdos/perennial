/-
Port of `src/Helpers/bytes.v`: bytes as lists of bits (least significant first).
-/
import Perennial.Std.ByteExplode
import Perennial.Std.List

namespace Perennial

/-- The 8 bits of a byte, least significant first. -/
def byteToBits (x : Byte) : List Bool := (List.range 8).map (fun i => x.toNat.testBit i)

@[len] theorem length_byte_to_bits (x : Byte) : (byteToBits x).length = 8 := by
  simp [byteToBits]

/-- The byte with bits `bs` (least significant first). -/
def bitsToByte (bs : List Bool) : Byte :=
  BitVec.ofNat 8 ((bs.mapIdx fun n b => if b then 2 ^ n else 0).foldr (· + ·) 0)

set_option maxRecDepth 10000 in
theorem byteToBits_to_byte (x : Byte) : bitsToByte (byteToBits x) = x := by
  revert x; apply byte_explode; decide +kernel

theorem explode_bits (bs : List Bool) (h : bs.length = 8) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 : Bool, bs = [b0, b1, b2, b3, b4, b5, b6, b7] := by
  match bs, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ => exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩

theorem bitsToByte_to_bits (bs : List Bool) (h : bs.length = 8) :
    byteToBits (bitsToByte bs) = bs := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩ := explode_bits bs h
  revert b0 b1 b2 b3 b4 b5 b6 b7; decide +kernel

theorem byteToBits_inj {b₁ b₂ : Byte} (h : byteToBits b₁ = byteToBits b₂) : b₁ = b₂ := by
  have := congrArg bitsToByte h
  rwa [byteToBits_to_byte, byteToBits_to_byte] at this

theorem bitsToByte_inj (bs₁ bs₂ : List Bool) (h1 : bs₁.length = 8) (h2 : bs₂.length = 8)
    (h : bitsToByte bs₁ = bitsToByte bs₂) : bs₁ = bs₂ := by
  have := congrArg byteToBits h
  rwa [bitsToByte_to_bits _ h1, bitsToByte_to_bits _ h2] at this

theorem byte_bit_ext_eq (b₁ b₂ : Byte)
    (h : ∀ off : Nat, off < 8 → byteToBits b₁ !! off = byteToBits b₂ !! off) : b₁ = b₂ := by
  apply byteToBits_inj
  apply List.ext_getElem?; intro i
  by_cases hi : i < 8
  · exact h i hi
  · rw [List.getElem?_eq_none (by rw [length_byte_to_bits]; omega),
      List.getElem?_eq_none (by rw [length_byte_to_bits]; omega)]

theorem lookup_byte_to_bits (byt : Byte) (i : Nat) (h : i < 8) :
    byteToBits byt !! i = some (decide (byt &&& ((1 : w8) <<< i) ≠ 0)) := by
  simp only [byteToBits, List.getElem?_map, List.getElem?_range h, Option.map_some,
    Option.some.injEq]
  have : ∀ off : Fin 8, ∀ b : Byte,
      b.toNat.testBit off = decide (b &&& ((1 : w8) <<< off.val) ≠ 0) := by
    intro off b; revert b; apply byte_explode; revert off; decide +kernel
  exact this ⟨i, h⟩ byt

/-- Rocq `bytesToBits`. -/
def bytesToBits (l : List Byte) : List Bool := (l.map byteToBits).flatten

@[len] theorem length_bytes_to_bits (b : List Byte) : (bytesToBits b).length = 8 * b.length := by
  induction b with
  | nil => rfl
  | cons x b ih => simp only [bytesToBits, List.map_cons, List.flatten_cons, List.length_append,
      length_byte_to_bits, List.length_cons] at *; rw [ih]; omega

theorem bytesToBits_app (a b : List Byte) :
    bytesToBits (a ++ b) = bytesToBits a ++ bytesToBits b := by
  simp [bytesToBits]

theorem bytesToBits_inj {a b : List Byte} (h : bytesToBits a = bytesToBits b) : a = b := by
  have := join_same_len_inj 8 (by decide) _ _ (by simp [length_byte_to_bits])
    (by simp [length_byte_to_bits]) h
  clear h
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons x a ih =>
    cases b with
    | nil => simp at this
    | cons y b =>
      simp only [List.map_cons, List.cons.injEq] at this
      rw [byteToBits_inj this.1, ih this.2]

end Perennial
