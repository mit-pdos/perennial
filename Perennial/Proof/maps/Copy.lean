/-
The proof of `maps.Copy`: Perennial's `for range` rule over the read-only `src` (`wp_map_for_range`);
before the `i`-th key, `dst` holds `src`'s entries at the first `i` keys over its own (`copyPrefix`).
-/
module

public import Perennial.Spec.maps.Copy

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std map

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : maps.Assumptions]

theorem maps.Copy.wp_proof : maps.Copy.spec (GF := GF) (hG := hG) := by
  intro K V _ _ _ _ _ Kt Vt M1 M2 _ _ _ _ _ _ _ dst src dq D S
  wp_start as ⟨Hd, Hs⟩
  wp_auto
  wp_apply (wp_map_for_range (fun keys i => iprop(
      "dst" ∷ dst_ptr ↦ dst ∗ "Hd" ∷ dst ↦$ (maps.copyPrefix S D (keys.take i.toNat)) ∗
      "k" ∷ (∃ kv : K, k_ptr ↦ kv) ∗ "v" ∷ (∃ vv : V, v_ptr ↦ vv) ∗
      "HΦ" ∷ (dst ↦$ (S ∪ D) ∗ src ↦${dq} S -∗ Φ #()) ∗
      "%Hi" ∷ ⌜0 ≤ i⌝))) $$ Hs
  iintro %keys ⟨%Hmem, %Hsize, %Hnd⟩
  isplitl [dst Hd k v HΦ]
  · iframe
    isplitl [Hd]
    · simp only [Int.toNat_zero, List.take_zero, maps.copyPrefix_nil]
      iexact Hd
    isplitl [k]
    · iexists _; iframe
    isplitl [v]
    · iexists _; iframe
    ipureintro; simp
  isplitr
  · imodintro
    iintro %i %key %vl ⟨%Hk, %Hlook⟩ ⟨dst, Hd, ⟨%kv, k⟩, ⟨%vv, v⟩, HΦ, %Hi⟩
    wp_auto
    wp_apply wp_mapInsert $$ Hd with Hd
    have htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hk]; rfl
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iframe
    isplitl [Hd]
    · rw [htake, ← maps.copyPrefix_snoc S D _ key vl Hlook]
      iexact Hd
    isplitl [k]
    · iexists _; iframe
    isplitl [v]
    · iexists _; iframe
    ipureintro; omega
  · iintro ⟨dst, Hd, k, v, HΦ, %Hi⟩ Hs
    wp_auto
    iapply HΦ
    iframe
    rw [show ((GMap.size S : Nat) : Int).toNat = keys.length by omega, List.take_length,
      maps.copyPrefix_all S D keys Hmem]
    iexact Hd

end proof

end Perennial
