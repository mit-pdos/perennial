/-
The proof of `slices.nextPowerOfTwo`.
-/
module

public import Perennial.Spec.slices.nextPowerOfTwo
public import Perennial.Spec.math.bits.Len
public import Perennial.Proof.slices.PartitionBasics

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

theorem slices.nextPowerOfTwo.wp_proof
    (wp_Len : math.bits.Len.spec (GF := GF) (hG := hG)) :
    slices.nextPowerOfTwo.spec (GF := GF) (hG := hG) := by
  intro length h
  wp_start
  wp_auto
  wp_apply wp_Len with %l %Hl
  wp_apply wp_shiftCount_int
  · ipureintro; have := Hl.1; word
  iapply HΦ
  ipureintro
  obtain ⟨_, Hlt, Hle⟩ := Hl
  have hu : uint.Z length = sint.Z length := by word
  rcases Hle with Hle | Hle
  · subst Hle; simp at h
  have hl63 : uint.nat l < 64 := by
    rcases Nat.lt_or_ge (uint.nat l) 64 with h' | h'
    · exact h'
    · exfalso
      have : (2 : Int) ^ 64 ≤ 2 ^ uint.nat l := by
        have := Nat.pow_le_pow_right (n := 2) (by decide) h'
        exact_mod_cast this
      have : uint.Z length < 2 ^ 63 := by word
      omega
  have hshift : uint.Z (W64 1 <<< l) = 2 ^ uint.nat l := by
    rw [show uint.Z (W64 1 <<< l) = ((W64 1 <<< l).toNat : Int) from rfl, BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft]
    simp only [show (W64 1).toNat = 1 from rfl, Nat.one_shiftLeft]
    rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (a := 2) (by decide) hl63)]
    norm_cast
  rw [hshift]
  omega

end proof

end Perennial
