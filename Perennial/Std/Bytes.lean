/-
Port of `src/Helpers/bytes.v`: bytes as lists of bits (least significant first).
-/
import Perennial.Std.ByteExplode
import Perennial.Std.List

namespace Perennial

/-- The 8 bits of a byte, least significant first. -/
def byte_to_bits (x : byte) : List Bool := (List.range 8).map (fun i => x.toNat.testBit i)

@[len] theorem length_byte_to_bits (x : byte) : (byte_to_bits x).length = 8 := by
  simp [byte_to_bits]

/-- The byte with bits `bs` (least significant first). -/
def bits_to_byte (bs : List Bool) : byte :=
  BitVec.ofNat 8 ((bs.mapIdx fun n b => if b then 2 ^ n else 0).foldr (· + ·) 0)

set_option maxRecDepth 10000 in
theorem byte_to_bits_to_byte (x : byte) : bits_to_byte (byte_to_bits x) = x := by
  revert x; apply byte_explode; decide +kernel

theorem explode_bits (bs : List Bool) (h : bs.length = 8) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 : Bool, bs = [b0, b1, b2, b3, b4, b5, b6, b7] := by
  match bs, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ => exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩

theorem bits_to_byte_to_bits (bs : List Bool) (h : bs.length = 8) :
    byte_to_bits (bits_to_byte bs) = bs := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩ := explode_bits bs h
  revert b0 b1 b2 b3 b4 b5 b6 b7; decide +kernel

theorem byte_to_bits_inj {b₁ b₂ : byte} (h : byte_to_bits b₁ = byte_to_bits b₂) : b₁ = b₂ := by
  have := congrArg bits_to_byte h
  rwa [byte_to_bits_to_byte, byte_to_bits_to_byte] at this

theorem bits_to_byte_inj (bs₁ bs₂ : List Bool) (h1 : bs₁.length = 8) (h2 : bs₂.length = 8)
    (h : bits_to_byte bs₁ = bits_to_byte bs₂) : bs₁ = bs₂ := by
  have := congrArg byte_to_bits h
  rwa [bits_to_byte_to_bits _ h1, bits_to_byte_to_bits _ h2] at this

theorem byte_bit_ext_eq (b₁ b₂ : byte)
    (h : ∀ off : Nat, off < 8 → byte_to_bits b₁ !! off = byte_to_bits b₂ !! off) : b₁ = b₂ := by
  apply byte_to_bits_inj
  apply List.ext_getElem?; intro i
  by_cases hi : i < 8
  · exact h i hi
  · rw [List.getElem?_eq_none (by rw [length_byte_to_bits]; omega),
      List.getElem?_eq_none (by rw [length_byte_to_bits]; omega)]

theorem lookup_byte_to_bits (byt : byte) (i : Nat) (h : i < 8) :
    byte_to_bits byt !! i = some (decide (byt &&& ((1 : w8) <<< i) ≠ 0)) := by
  simp only [byte_to_bits, List.getElem?_map, List.getElem?_range h, Option.map_some,
    Option.some.injEq]
  have : ∀ off : Fin 8, ∀ b : byte,
      b.toNat.testBit off = decide (b &&& ((1 : w8) <<< off.val) ≠ 0) := by
    intro off b; revert b; apply byte_explode; revert off; decide +kernel
  exact this ⟨i, h⟩ byt

/-- Rocq `bytes_to_bits`. -/
def bytes_to_bits (l : List byte) : List Bool := (l.map byte_to_bits).flatten

@[len] theorem length_bytes_to_bits (b : List byte) : (bytes_to_bits b).length = 8 * b.length := by
  induction b with
  | nil => rfl
  | cons x b ih => simp only [bytes_to_bits, List.map_cons, List.flatten_cons, List.length_append,
      length_byte_to_bits, List.length_cons] at *; rw [ih]; omega

theorem bytes_to_bits_app (a b : List byte) :
    bytes_to_bits (a ++ b) = bytes_to_bits a ++ bytes_to_bits b := by
  simp [bytes_to_bits]

theorem bytes_to_bits_inj {a b : List byte} (h : bytes_to_bits a = bytes_to_bits b) : a = b := by
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
      rw [byte_to_bits_inj this.1, ih this.2]

end Perennial
