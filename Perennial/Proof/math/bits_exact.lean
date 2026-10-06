/-
Exact specs of `math/bits.Len64` and `math/bits.Len` (`Perennial/Proof/math/bits.lean`
only proves that they return some value, as in Rocq). Used for
`slices.nextPowerOfTwo` (`wp_breakPatternsCmpFunc`).
-/
import Perennial.Proof.math.bits

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace math.bits

/-- bit length of a byte -/
def blen8 (i : Nat) : Nat :=
  if i < 1 then 0 else if i < 2 then 1 else if i < 4 then 2 else if i < 8 then 3 else
  if i < 16 then 4 else if i < 32 then 5 else if i < 64 then 6 else if i < 128 then 7 else 8

theorem len8tab_lookup {s : GoString} (h : s = (List.range 256).map (fun i => W8 (blen8 i))) :
    ∀ i < 256, s[i]? = some (W8 (blen8 i)) := by
  intro i hi; subst h; simp [hi]

-- (one list comparison instead of 256 lookups)
set_option maxRecDepth 10000 in
theorem len8tab_exact [FfiSyntax] [GoGlobalContext] :
    ∃ s : GoString, len8tab = #s ∧ s.length = 256 ∧
      ∀ i < 256, s[i]? = some (W8 (blen8 i)) :=
  ⟨_, rfl, rfl, len8tab_lookup (by decide)⟩

set_option maxRecDepth 10000 in
theorem blen8_spec (i : Nat) (h : i < 256) :
    i < 2 ^ blen8 i ∧ (i = 0 ∨ 2 ^ blen8 i ≤ 2 * i) ∧ blen8 i ≤ 8 := by
  revert i; decide

theorem len_fin (x l : w64) (n i : Nat) (hi : i = uint.nat x / 2 ^ n) (hi256 : i < 256)
    (hn : n ≤ 56) (hpos : n = 0 ∨ 2 ^ n ≤ uint.nat x) (hl : uint.nat l = n + blen8 i) :
    uint.Z l ≤ 64 ∧ uint.Z x < 2 ^ uint.nat l ∧ (x = 0 ∨ 2 ^ uint.nat l ≤ 2 * uint.Z x) := by
  obtain ⟨h1, h2, h3⟩ := blen8_spec i hi256
  have hN : 0 < 2 ^ n := Nat.two_pow_pos n
  have hxl : uint.nat x < 2 ^ n * 2 ^ blen8 i := by
    rw [Nat.mul_comm]; exact (Nat.div_lt_iff_lt_mul hN).1 (hi ▸ h1)
  have hdm : i * 2 ^ n ≤ uint.nat x := hi ▸ Nat.div_mul_le_self _ _
  have hzx : uint.Z x = (uint.nat x : Int) := by word
  refine ⟨?_, ?_, ?_⟩
  · have : uint.Z l = (uint.nat l : Int) := by word
    omega
  · have : (2 : Int) ^ (n + blen8 i) = ((2 ^ n * 2 ^ blen8 i : Nat) : Int) := by
      rw [← Nat.pow_add]; norm_cast
    rw [hl, this, hzx]; exact_mod_cast hxl
  · rcases h2 with h2 | h2
    · left
      subst h2
      rcases hpos with hpos | hpos
      · subst hpos; simp at hi; word
      · have := Nat.div_pos hpos hN; omega
    · right
      have e : (2 : Int) ^ (n + blen8 i) = ((2 ^ n * 2 ^ blen8 i : Nat) : Int) := by
        rw [← Nat.pow_add]; norm_cast
      rw [hl, e, hzx]
      have : 2 ^ n * 2 ^ blen8 i ≤ 2 * uint.nat x := by
        calc 2 ^ n * 2 ^ blen8 i ≤ 2 ^ n * (2 * i) := Nat.mul_le_mul_left _ h2
          _ = 2 * (i * 2 ^ n) := by rw [Nat.mul_comm i, Nat.mul_left_comm]
          _ ≤ 2 * uint.nat x := Nat.mul_le_mul_left _ hdm
      exact_mod_cast this

theorem len_fin' (x l : w64) (b : w8) (n i : Nat) (heq : W8 (blen8 i) = b)
    (hl : uint.nat l = n + uint.nat b) (hn : n ≤ 56) (hi : i = uint.nat x / 2 ^ n)
    (hi256 : i < 256) (hpos : n = 0 ∨ 2 ^ n ≤ uint.nat x) :
    uint.Z l ≤ 64 ∧ uint.Z x < 2 ^ uint.nat l ∧ (x = 0 ∨ 2 ^ uint.nat l ≤ 2 * uint.Z x) := by
  have := (blen8_spec i hi256).2.2
  refine len_fin x l n i hi hi256 hn hpos ?_
  rw [hl, ← heq]; word

/-- The state of `Len64` after shifting `x` (initially `X`) right by `n` bits: `x < 2 ^ b`. -/
def LenInv (X b : Nat) (x n : w64) : Prop :=
  uint.nat x = X / 2 ^ uint.nat n ∧ uint.nat x < 2 ^ b ∧ uint.nat n + b ≤ 64 ∧
    (uint.nat n = 0 ∨ 2 ^ uint.nat n ≤ X)

theorem lenInv_init (X : Nat) (x : w64) (hX : uint.nat x = X) :
    LenInv X 64 x (zero_val w64) := by
  have := x.isLt
  simp only [LenInv, zero_val, ZeroVal.zeroValDef]
  refine ⟨?_, ?_, ?_, Or.inl ?_⟩ <;> simp [uint.nat] at * <;> omega

theorem lenInv_yes (X s : Nat) (x n x' n' : w64) (h : LenInv X (2 * s) x n)
    (hge : 2 ^ s ≤ uint.nat x) (hx' : uint.nat x' = uint.nat x / 2 ^ s)
    (hn' : uint.nat n' = uint.nat n + s) : LenInv X s x' n' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, by omega, Or.inr ?_⟩
  · rw [hx', hn', h1, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  · rw [hx', Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s), ← Nat.pow_add,
      show s + s = 2 * s by omega]
    exact h2
  · rw [hn', Nat.pow_add, Nat.mul_comm]
    rw [h1] at hge
    exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).1 hge

theorem lenInv_no (X s : Nat) (x n : w64) (h : LenInv X (2 * s) x n)
    (hlt : uint.nat x < 2 ^ s) : LenInv X s x n :=
  ⟨h.1, hlt, by have := h.2.2.1; omega, h.2.2.2⟩

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.bits.Assumptions]

theorem wp_Len64_exact (x : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.math.bits }}
      (App (Val (@! Len64)) (Val #x))
    {{ (l : w64), RET #l; ⌜uint.Z l ≤ 64 ∧ uint.Z x < 2 ^ uint.nat l ∧
        (x = 0 ∨ 2 ^ uint.nat l ≤ 2 * uint.Z x)⌝ }} := by
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
  rw [hidx, htab _ hx3']
  wp_auto
  wp_end
  ipureintro
  have := (blen8_spec _ hx3').2.2
  exact len_fin' x _ _ (uint.nat n3) (uint.nat x3) rfl (by word) (by omega) hi hx3' hpos

theorem wp_Len_exact (x : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.math.bits }}
      (App (Val (@! Len)) (Val #x))
    {{ (l : w64), RET #l; ⌜uint.Z l ≤ 64 ∧ uint.Z x < 2 ^ uint.nat l ∧
        (x = 0 ∨ 2 ^ uint.nat l ≤ 2 * uint.Z x)⌝ }} := by
  wp_start
  wp_auto
  wp_apply wp_Len64_exact with %l %Hl
  wp_end

end wps

end math.bits

end Perennial
end
