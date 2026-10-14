/-
The proof of `math.bits.Len64`.
-/
module

public import Perennial.Spec.math.bits.Len64
public import Perennial.Proof.math.bits.Exact

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : math.bits.Assumptions]

/-- The three `if x >= 1<<k { x >>= k; n += k }` steps keep `LenInv`; the final lookup in
`len8tab` (`len8tab_exact`, one list comparison instead of 256 lookups) adds the bit length
of the remaining byte. -/
theorem math.bits.Len64.wp_proof : math.bits.Len64.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  obtain ⟨s, hs, hlen, htab⟩ := len8tab_exact
  rw [hs]
  clear hs
  wp_auto
  -- the three `if x >= 1<<k { x >>= k; n += k }` statements, joined at `LenInv`
  wp_join iprop(∃ (x' n' : w64), "x" ∷ x_ptr ↦ x' ∗ "n" ∷ n_ptr ↦ n' ∗
      "%Hinv" ∷ ⌜LenInv (uint.nat x) 32 x' n'⌝) with [x n] as ⟨%x1, %n1, x, n, %Hinv⟩
  · iexists _, _; iframe; ipureintro
    exact lenInv_yes _ 32 x (zero_val w64) _ _ (lenInv_init _ x rfl) (by word) (by word)
      (by simp only [zero_val, ZeroVal.zeroValDef]; word)
  · iexists _, _; iframe; ipureintro
    exact lenInv_no _ 32 x _ (lenInv_init _ x rfl) (by word)
  wp_join iprop(∃ (x' n' : w64), "x" ∷ x_ptr ↦ x' ∗ "n" ∷ n_ptr ↦ n' ∗
      "%Hinv" ∷ ⌜LenInv (uint.nat x) 16 x' n'⌝) with [x n] as ⟨%x2, %n2, x, n, %Hinv⟩
  · iexists _, _; iframe; ipureintro
    exact lenInv_yes _ 16 x1 n1 _ _ Hinv (by word) (by word) (by have := Hinv.2.2.1; word)
  · iexists _, _; iframe; ipureintro
    exact lenInv_no _ 16 x1 n1 Hinv (by word)
  wp_join iprop(∃ (x' n' : w64), "x" ∷ x_ptr ↦ x' ∗ "n" ∷ n_ptr ↦ n' ∗
      "%Hinv" ∷ ⌜LenInv (uint.nat x) 8 x' n'⌝) with [x n] as ⟨%x3, %n3, x, n, %Hinv⟩
  · iexists _, _; iframe; ipureintro
    exact lenInv_yes _ 8 x2 n2 _ _ Hinv (by word) (by word) (by have := Hinv.2.2.1; word)
  · iexists _, _; iframe; ipureintro
    exact lenInv_no _ 8 x2 n2 Hinv (by word)
  -- `return n + int(len8tab[x])`
  obtain ⟨hi, hx3, hn3, hpos⟩ := Hinv
  have hx3' : uint.nat x3 < 256 := hx3
  have hidx : sint.nat (W64 (uint.Z (W8 (uint.Z x3)))) = uint.nat x3 := by word
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 (uint.Z (W8 (uint.Z x3)))) by word), hidx, htab _ hx3']
  wp_auto
  wp_end
  ipureintro
  have := (blen8_spec _ hx3').2.2
  exact len_fin' x _ _ (uint.nat n3) (uint.nat x3) rfl (by word) (by omega) hi hx3' hpos

end proof

end Perennial
