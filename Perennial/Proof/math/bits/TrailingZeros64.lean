/-
The proof of `math.bits.TrailingZeros64`.
-/
module

public import Perennial.Spec.math.bits.TrailingZeros64

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace math.bits

/-- `x & -x` is `x` for a power of two (checked for each of the 64). -/
theorem pow2_and_neg : ∀ k : Fin 64, (W64 (2 ^ k.val) &&& -W64 (2 ^ k.val)) = W64 (2 ^ k.val) := by
  decide +kernel

/-- `deBruijn64tab` holds the exponent of a power of two at `2 ^ k * deBruijn64 >> 58` (checked
for each of the 64). -/
theorem deBruijn64tab_pow2 : ∀ k : Fin 64,
    deBruijn64tabVal.arr[((W64 (2 ^ k.val) * W64 0x03f79d71b4ca8b09) >>> (W64 58)).toNat]? =
      some (W8 k.val) := by
  decide +kernel

/-- The lookup's index is below 64. -/
theorem shiftRight58_lt (y : w64) : (y >>> (W64 58)).toNat < 64 := by
  have := y.isLt
  show (y >>> (58 : Nat)).toNat < 64
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

end math.bits

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.bits.Assumptions]

/-- `deBruijn64` converted to `uint64`, as a variable: a separate lemma, so that the steps of
`TrailingZeros64` see a variable in place of the literal (with the literal in place, Lean's kernel
recursed too deep checking the array index's step). -/
theorem math.bits.wp_convert_deBruijn64 (Φ : val → IProp GF) :
    (∀ y : w64, ⌜y = W64 285870213051353865⌝ -∗ Φ #y) ⊢
      WP (App (Val (GoInstruction (Convert go.untypedInt go.uint64))) (Val math.bits.deBruijn64))
        {{ Φ }} := by
  iintro H
  wp_auto
  iapply H
  ipureintro; rfl

/-- `x & -x` is `x` itself for a power of two, at which `deBruijn64tab` holds its exponent
(`deBruijn64tab_pow2`, checked for each of the 64). -/
theorem math.bits.TrailingZeros64.wp_proof : math.bits.TrailingZeros64.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  ihave #Htab := math.bits.isInit_access $$ Hpkg
  generalize hd : math.bits.deBruijn64 = dv
  wp_auto
  wp_if_destruct
  · wp_end
  wp_bind (App (Val (GoInstruction (Convert go.untypedInt go.uint64))) (Val dv))
  subst hd
  iapply math.bits.wp_convert_deBruijn64
  iintro %y %hy
  wp_auto
  generalize hidx : ((x &&& -x) * y) >>> W64 58 = idx
  have hlt : idx.toNat < 64 := by rw [← hidx]; exact math.bits.shiftRight58_lt _
  have hs : sint.Z idx = idx.toNat := by word
  rw [hs, if_pos ⟨by omega, by omega⟩]
  obtain ⟨v, hv⟩ : ∃ v, math.bits.deBruijn64tabVal.arr[idx.toNat]? = some v :=
    ⟨_, List.getElem?_eq_getElem (by simp [math.bits.deBruijn64tabVal]; omega)⟩
  icases array_acc (V := w8) _ (idx.toNat : Int) _ _ _ v (by omega) (by simpa using hv) $$ Htab
    with ⟨Hv, -⟩
  wp_auto
  wp_end
  ipureintro
  refine ⟨fun h0 => absurd h0 Hif, fun k hk hx => ?_⟩
  subst hx hy
  have h2 := math.bits.pow2_and_neg ⟨k, hk⟩
  have h3 := math.bits.deBruijn64tab_pow2 ⟨k, hk⟩
  simp only at h2 h3
  rw [h2] at hidx
  rw [show (W64 0x03f79d71b4ca8b09) = W64 285870213051353865 from rfl, hidx, hv] at h3
  cases h3
  word
end proof

end Perennial
