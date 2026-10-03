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

set_option maxRecDepth 100000 in
theorem len8tab_exact [ffi_syntax] [GoGlobalContext] :
    ∃ s : go_string, len8tab = #s ∧ s.length = 256 ∧
      ∀ i < 256, s[i]? = some (W8 (blen8 i)) :=
  ⟨_, rfl, rfl, by decide⟩

theorem blen8_spec (i : Nat) (h : i < 256) :
    i < 2 ^ blen8 i ∧ (i = 0 ∨ 2 ^ blen8 i ≤ 2 * i) ∧ blen8 i ≤ 8 := by
  unfold blen8
  repeat' split
  all_goals (simp only [Nat.reducePow]; omega)

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

set_option hygiene false in
/-- Finish a branch of `Len64` that returned `n + len8tab[...]`. -/
macro "len_finish " n:num : tactic =>
  `(tactic| (refine len_fin' _ _ _ $n _ heq ?_ (by decide) ?_ ?_ ?_ <;> word))

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.bits.Assumptions]

set_option maxRecDepth 100000 in
theorem wp_Len64_exact (x : w64) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.math.bits }}
      (App (Val (@! Len64)) (Val #x))
    {{ (l : w64), RET #l; ⌜uint.Z l ≤ 64 ∧ uint.Z x < 2 ^ uint.nat l ∧
        (x = 0 ∨ 2 ^ uint.nat l ≤ 2 * uint.Z x)⌝ }} := by
  wp_start
  obtain ⟨s, hs, hlen, htab⟩ := len8tab_exact
  rw [hs]
  clear hs
  wp_auto
  wp_if_destruct <;> wp_if_destruct <;> wp_if_destruct
  all_goals wp_pures
  all_goals split
  all_goals rename_i heq
  all_goals (first
    | (rw [htab _ (by word)] at heq)
    | (have := (htab _ (by word)); rw [this] at heq))
  all_goals (try simp only [Option.some.injEq] at heq)
  all_goals (try (exfalso; exact heq _ rfl))
  all_goals (wp_auto; wp_end; ipureintro; (try simp only [zero_val, ZeroVal.zero_val_def]))
  -- the branches, in order, shifted `x` by 32+16+8, 32+16, 32+8, 32, 16+8, 16, 8, 0 bits
  · len_finish 56
  · len_finish 48
  · len_finish 40
  · len_finish 32
  · len_finish 24
  · len_finish 16
  · len_finish 8
  · len_finish 0

theorem wp_Len_exact (x : w64) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.math.bits }}
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
