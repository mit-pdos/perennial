import Perennial.Std.Word.Automation
import Perennial.Std.ListBasics

namespace Perennial

/-- The character with this byte as its code. -/
def u8ToAscii (x : Byte) : Char := Char.ofNat x.toNat

/-- The one-character string of this byte. -/
def u8ToString (x : Byte) : String := String.singleton (u8ToAscii x)

/-- `u64RoundUp x div`: `(x + div) / div * div`. -/
def u64RoundUp (x div : U64) : U64 := (x + div) / div * div

theorem seq_U64_NoDup (m len : Int) (hlb : 0 ≤ m) (hub : m + len < 2 ^ 64) :
    ((seqZ m len).map W64).Nodup := by
  unfold List.Nodup
  rw [List.pairwise_map]
  refine (NoDup_seqZ m len).imp_of_mem (fun {a b} ha hb hab e => hab ?_)
  rw [elem_of_seqZ] at ha hb
  have := congrArg uint.Z e
  rwa [uint_Z_W64 a (by omega) (by omega), uint_Z_W64 b (by omega) (by omega)] at this

theorem w64_to_nat_id (x : w64) : W64 (uint.nat x : Int) = x := by
  simp [W64, uint.nat]

theorem uint_nat_inj {n : Nat} (w₀ w₁ : BitVec n) (h : uint.nat w₀ = uint.nat w₁) : w₀ = w₁ :=
  BitVec.eq_of_toNat_eq h

end Perennial
