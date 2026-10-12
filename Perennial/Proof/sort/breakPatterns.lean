/-
The proof of `sort.breakPatterns` over a `sort.Interface`: the proof of `slices.breakPatternsCmpFunc`
(`Perennial/Proof/slices/breakPatternsCmpFunc.lean`) with `Less`/`Swap` calls.
-/
module

public import Perennial.Spec.sort.breakPatterns
public import Perennial.Spec.sort.nextPowerOfTwo
public import Perennial.Spec.sort.xorshift__Next
public import Perennial.Proof.sort.SorterBasics
public import Perennial.Proof.sort.PartitionBasics
public import Perennial.Proof.slices.PartitionBasics

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open slices

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

theorem sort.breakPatterns.wp_proof
    (wp_nextPowerOfTwo : sort.nextPowerOfTwo.spec (GF := GF) (hG := hG))
    (wp_xorshift_Next : sort.xorshift.Next.spec (GF := GF) (hG := hG)) :
    sort.breakPatterns.spec (GF := GF) (hG := hG) := fun {E} x own R _ a b xs => by
  -- (`fun`, not `intro`: `wp_apply_post` runs `whnfR` outside the goal's context, so a
  -- `wp_apply` fails silently on binders introduced by a tactic)
  wp_start as H
  iNamed H
  wp_auto
  wp_if_destruct
  · wp_apply wp_nextPowerOfTwo _ (by word) with %m %Hm
    have hL : sint.Z (b - a) = sint.Z b - sint.Z a := by word
    have hd : sint.Z (BitVec.sdiv (b - a) (W64 4)) = (sint.Z b - sint.Z a) / 4 := by
      rw [sint_sdiv4 _ (by omega), hL]
    ihave HI : (∃ (xs1 : List E) (idx_val : w64) (rv : xorshift),
        "Hxs" ∷ own xs1 ∗
        "idx" ∷ idx_ptr ↦ idx_val ∗
        "random" ∷ random_ptr ↦ rv ∗
        "%idx_bound" ∷ ⌜sint.Z a + (sint.Z b - sint.Z a) / 4 * 2 - 1 ≤ sint.Z idx_val ∧
          sint.Z idx_val ≤ sint.Z a + (sint.Z b - sint.Z a) / 4 * 2 + 2⌝ ∗
        "%HPerm1" ∷ ⌜xs ≡ₚ xs1⌝ ∗
        "%Houtside1" ∷ ⌜OutsideSame xs xs1 (sint.nat a) (sint.nat b)⌝ : IProp GF) $$ [Hxs idx random]
    · iexists xs, _, _
      iframe
      ipureintro
      exact ⟨by word, List.Perm.refl _, outsideSame_refl _ _ _⟩
    wp_for HI
    wp_if_destruct
    · wp_apply wp_xorshift_Next $$ random with %rv' %n random
      have hand : uint.Z (n &&& (m - W64 1)) ≤ uint.Z (m - W64 1) := by
        have := Nat.and_le_right (n := n.toNat) (m := (m - W64 1).toNat)
        simp only [uint.Z, BitVec.toNat_and]; omega
      have hm1 : uint.Z (m - W64 1) = uint.Z m - 1 := by word
      have ho : sint.Z (n &&& (m - W64 1)) = uint.Z (n &&& (m - W64 1)) := by
        have h63 : uint.Z (n &&& (m - W64 1)) < 2 ^ 63 := by omega
        exact BitVec.toInt_eq_toNat_of_lt (by unfold uint.Z at h63; omega)
      have Hl := HPerm1.length_eq
      wp_join iprop(∃ o : w64, "other" ∷ other_ptr ↦ o ∗ "length" ∷ length_ptr ↦ (b - a) ∗
          "%Ho" ∷ ⌜0 ≤ sint.Z o ∧ sint.Z o < sint.Z b - sint.Z a⌝) with [other length]
          as ⟨%o, other, length, %Ho⟩
      · (try wp_auto); iexists _; iframe; ipureintro; constructor <;> word
      · (try wp_auto); iexists _; iframe; ipureintro; constructor <;> word
      have hj : sint.Z a ≤ sint.Z (a + o) ∧ sint.Z (a + o) < sint.Z b := by
        constructor <;> word
      generalize hjdef : (a + o) = j at *
      have hi : sint.Z a ≤ sint.Z idx_val ∧ sint.Z idx_val < sint.Z b := by
        have := hd; constructor <;> word
      list_elem xs1 (sint.nat j) as xo
      list_elem xs1 (sint.nat idx_val) as xi
      wp_apply wp_sorter_Swap_raw x own R xs1 idx_val j xi xo (by word) (by word)
        Hxi_lookup Hxo_lookup $$ [$Hsrt $Hxs] as Hxs
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro
      refine ⟨by have := hd; word, ?_, ?_⟩
      · exact HPerm1.trans (swap_perm xs1 (sint.nat j) (sint.nat idx_val) xo xi
          Hxo_lookup Hxi_lookup)
      · exact outsideSame_trans _ _ _ _ _ Houtside1
          (outsideSame_swap _ _ _ _ _ _ _ ⟨by word, by word⟩ ⟨by word, by word⟩)
    · iapply HΦ
      iframe
      ipureintro
      exact ⟨HPerm1, Houtside1⟩
  · iapply HΦ
    iframe
    ipureintro
    exact ⟨List.Perm.refl _, outsideSame_refl _ _ _⟩

end proof

end Perennial
