/-
Little-endian encoding of numbers as bytes. The byte sequences are lists, and
the numbers are `Nat`s.
-/
import Perennial.Std.Word

namespace Perennial

namespace LittleEndian

/-- The number with little-endian byte representation `bs`. -/
def combine : List w8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * combine bs

/-- The `n`-byte little-endian representation of `w` (mod `2^(8n)`). -/
def split : Nat → Nat → List w8
  | 0, _ => []
  | n + 1, w => BitVec.ofNat 8 w :: split n (w / 256)

theorem combine_unfold (b : w8) (bs : List w8) :
    combine (b :: bs) = b.toNat + 256 * combine bs := rfl

theorem length_split (n w : Nat) : (split n w).length = n := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih => simp [split, ih]

theorem combine_split (n z : Nat) : combine (split n z) = z % 2 ^ (n * 8) := by
  induction n generalizing z with
  | zero => simp [split, combine, Nat.mod_one]
  | succ n ih =>
    simp only [split, combine, ih, BitVec.toNat_ofNat]
    rw [show (n + 1) * 8 = 8 + n * 8 by omega, Nat.pow_add, Nat.mod_mul]

theorem combine_bound (bs : List w8) : combine bs < 2 ^ (8 * bs.length) := by
  induction bs with
  | nil => simp [combine]
  | cons b bs ih =>
    simp only [combine, List.length_cons]
    have := b.isLt
    rw [show 8 * (bs.length + 1) = 8 + 8 * bs.length by omega, Nat.pow_add]
    have : 256 * combine bs + 256 ≤ 256 * 2 ^ (8 * bs.length) := by
      have := Nat.mul_le_mul_left 256 (Nat.succ_le_of_lt ih); omega
    simp only [Nat.reducePow] at *; omega

theorem split_combine (n : Nat) (bs : List w8) (h : bs.length = n) : split n (combine bs) = bs := by
  induction bs generalizing n with
  | nil => subst h; rfl
  | cons b bs ih =>
    subst h
    show BitVec.ofNat 8 (b.toNat + 256 * combine bs) ::
      split bs.length ((b.toNat + 256 * combine bs) / 256) = b :: bs
    have := b.isLt
    rw [List.cons.injEq]
    constructor
    · apply BitVec.eq_of_toNat_eq; simp; omega
    · rw [show (b.toNat + 256 * combine bs) / 256 = combine bs by omega]
      exact ih _ rfl

end LittleEndian

end Perennial
