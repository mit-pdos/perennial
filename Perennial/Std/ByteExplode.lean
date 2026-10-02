/-
Port of `src/Helpers/byte_explode.v`: proving a property of every byte (or
small offset) by enumerating the cases.

Rocq's `byte_explode` takes 256 hypotheses `P (W8 0)`, ..., `P (W8 255)`; here
they are bundled as `∀ i : Fin 256, P (BitVec.ofNat 8 i)`, which `decide` can
often discharge for a computable `P`.
-/
import Perennial.Std.Word.Automation

namespace Perennial

theorem byte_explode (P : u8 → Prop) (h : ∀ i : Fin 256, P (BitVec.ofNat 8 i)) : ∀ x, P x := by
  intro x
  have := h ⟨x.toNat, x.isLt⟩
  simpa using this

theorem bit_off_explode (P : u64 → Prop) (h : ∀ i : Fin 8, P (W64 i)) :
    ∀ bit : u64, uint.Z bit < 8 → P bit := by
  intro bit hb
  have := h ⟨bit.toNat, by simp [uint.Z] at hb; omega⟩
  have e : W64 (bit.toNat : Int) = bit := by simp [W64]
  simpa [e] using this

theorem nat_off_explode (P : Nat → Prop) (h : ∀ i : Fin 8, P i) : ∀ off, off < 8 → P off :=
  fun off hoff => h ⟨off, hoff⟩

theorem Z_off_explode (P : Int → Prop) (h : ∀ i : Fin 8, P i) : ∀ off : Int, 0 ≤ off ∧ off < 8 → P off := by
  intro off hoff
  have := h ⟨off.toNat, by omega⟩
  simpa [Int.toNat_of_nonneg hoff.1] using this

/-- Rocq `byte_cases b`: prove a goal about byte `b` by checking all 256 values. -/
macro "byte_cases " b:term : tactic =>
  `(tactic| (revert $b:term; apply byte_explode; decide))

end Perennial
