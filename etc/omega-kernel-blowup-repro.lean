import Perennial.Std.Word.Automation
namespace Perennial
theorem kk (pos ws rs rwt r : BitVec 32) (num_readers : Nat)
  (Hf1 : BitVec.toNat rwt = 0)
  (Hf2 : BitVec.toNat ws = 0)
  (Hf3 : BitVec.toInt pos = ↑(num_readers + 1) + BitVec.toInt r + ↑(BitVec.toNat rs))
  (e : (BitVec.toInt pos).toNat = 1 + (BitVec.toInt (pos - 1#32)).toNat)
  (h1a : 2 * BitVec.toNat pos < 4294967296)
  (h1b : BitVec.toInt pos = ↑(BitVec.toNat pos)) :
  ¬(4294967296 ≤ 2 * ((BitVec.toNat pos + 4294967295) % 4294967296) ∧ BitVec.toInt (pos + BitVec.ofNat 32 4294967295) = ↑((BitVec.toNat pos + 4294967295) % 4294967296) - ((4294967296 : Nat) : Int)) := by
  omega
end Perennial
