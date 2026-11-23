/-
The proof of `maps.Clone` (of its trusted model, `TrustedCode/maps.lean`).
-/
module

public import Perennial.Spec.maps.Clone

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

theorem maps.Clone.wp_proof :
    maps.Clone.spec (GF := GF) (hG := hG) := by
  intro K V _ _ _ _ _ Kt Vt _ _ _ _ _
  constructor
  · intro m dq M
    wp_start as Hm
    ihave %Hnn := ownMap_not_nil _ _ _ $$ Hm
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_map_len $$ Hm with Hm
    wp_apply (wp_map_make2 (K := K) (V := V)) with %r Hr
    wp_apply (wp_map_for_range (fun keys i => iprop(
        "r" ∷ r_ptr ↦ r ∗ "Hr" ∷ r ↦$ maps.restrict M (keys.take i.toNat) ∗
        "k" ∷ (∃ kv : K, k_ptr ↦ kv) ∗ "v" ∷ (∃ vv : V, v_ptr ↦ vv) ∗
        "%Hi" ∷ ⌜0 ≤ i⌝))) $$ Hm
    iintro %keys ⟨%Hmem, %Hsize, %Hnd⟩
    isplitl [r Hr k v]
    · rw [show (List.take (Int.toNat 0) keys) = [] by simp, maps.restrict_nil]
      iframe
      isplitl [k]
      · iexists _; iframe
      isplitl [v]
      · iexists _; iframe
      ipureintro; omega
    isplitr
    · imodintro
      iintro %i %key %vl ⟨%Hk, %Hlook⟩ ⟨r, Hr, ⟨%kv, k⟩, ⟨%vv, v⟩, %Hi⟩
      have htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
        rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hk]; rfl
      wp_auto
      wp_apply wp_mapInsert $$ Hr with Hr
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      rw [htake, maps.restrict_snoc M _ key vl Hlook]
      iframe
      isplitl [k]
      · iexists _; iframe
      isplitl [v]
      · iexists _; iframe
      ipureintro; omega
    · iintro ⟨r, Hr, k, v, %Hi⟩ Hm
      rw [show ((GMap.size M : Nat) : Int).toNat = keys.length by omega, List.take_length,
        maps.restrict_all M keys (fun k h => (Hmem k).2 h)]
      wp_auto
      iapply HΦ
      iframe
  · wp_start
    wp_auto
    iapply HΦ
    itrivial

end proof

end Perennial
