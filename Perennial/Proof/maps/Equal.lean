/-
The proof of `maps.Equal`.
-/
module

public import Perennial.Spec.maps.Equal

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

theorem maps.Equal.wp_proof :
    maps.Equal.spec (GF := GF) (hG := hG) := by
  intro K V _ _ _ _ _ _ Kt Vt T1 T2 _ _ _ _ _ _ _ _ m1 m2 dq1 dq2 M1 M2
  wp_start as ⟨Hm1, Hm2⟩
  wp_auto
  wp_apply wp_map_len_lt $$ Hm1 with ⟨Hm1, %Hlt1⟩
  wp_apply wp_map_len_lt $$ Hm2 with ⟨Hm2, %Hlt2⟩
  have hw : W64 (GMap.size M1 : Int) = W64 (GMap.size M2 : Int) ↔ GMap.size M1 = GMap.size M2 := by
    constructor
    · intro h; word
    · intro h; rw [h]
  by_cases hs : GMap.size M1 = GMap.size M2
  · rw [decide_eq_true (hw.2 hs)]
    wp_auto
    wp_apply (wp_map_for_range (fun keys i => iprop(
        "m2" ∷ m2_ptr ↦ m2 ∗ "Hm2" ∷ m2 ↦${dq2} M2 ∗ "res0" ∷ «$res0_ptr» ↦ false ∗
        "k" ∷ (∃ kv : K, k_ptr ↦ kv) ∗ "v1" ∷ (∃ vv : V, v1_ptr ↦ vv) ∗ "HΦ" ∷ (∀ b : Bool, ⌜b = true ↔ M1 = M2⌝ ∗ m1 ↦${dq1} M1 ∗ m2 ↦${dq2} M2 -∗ Φ #b) ∗
        "%Hag" ∷ ⌜∀ key ∈ keys.take i.toNat, M2 !! key = M1 !! key⌝ ∗
        "%Hi" ∷ ⌜0 ≤ i⌝))) $$ Hm1
    iintro %keys ⟨%Hmem, %Hsize, %Hnd⟩
    isplitl [m2 Hm2 «$res0» k v1 HΦ]
    · iframe
      isplitl [k]
      · iexists _; iframe
      isplitl [v1]
      · iexists _; iframe
      ipureintro; simp
    isplitr
    · imodintro
      iintro %i %key %vl ⟨%Hk, %Hlook⟩ ⟨m2, Hm2, res0, ⟨%kv, k⟩, ⟨%vv, v1⟩, HΦ, %Hag, %Hi⟩
      wp_auto
      wp_apply wp_map_lookup2 $$ Hm2 with Hm2
      have htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
        rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hk]; rfl
      cases h2 : M2 !! key with
      | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Option.getD_none]
        wp_auto
        unfold forMapPostcondition
        iright; iright; iright; ileft
        iexists #()
        isplitr
        · ipureintro; rfl
        iintro Hm1
        wp_auto
        iapply HΦ
        iframe
        ipureintro
        constructor
        · intro h; cases h
        · intro h; subst h; rw [Hlook] at h2; cases h2
      | some w =>
        haveI := go.tagged_steps _ _ _ _ (go.is_strictly_comparable (t := Vt) (V := V) vl w)
        by_cases hvw : vl = w
        · subst hvw
          simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
          wp_auto
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iframe
          isplitl [k]
          · iexists _; iframe
          isplitl [v1]
          · iexists _; iframe
          ipureintro
          refine ⟨?_, by omega⟩
          intro k' hk'
          rw [htake, List.mem_append, List.mem_singleton] at hk'
          rcases hk' with hk' | rfl
          · exact Hag k' hk'
          · rw [h2, Hlook]
        · simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
          wp_auto
          rw [decide_eq_false hvw]
          wp_auto
          unfold forMapPostcondition
          iright; iright; iright; ileft
          iexists #()
          isplitr
          · ipureintro; rfl
          iintro Hm1
          wp_auto
          iapply HΦ
          iframe
          ipureintro
          constructor
          · intro h; cases h
          · intro h; subst h; rw [Hlook] at h2; exact absurd (Option.some.inj h2) hvw
    · iintro ⟨m2, Hm2, res0, k, v1, HΦ, %Hag, %Hi⟩ Hm1
      wp_auto
      iapply HΦ
      iframe
      ipureintro
      constructor
      · intro _
        apply maps.gmap_eq_of_subseteq_size _ hs
        intro k' v hv
        have hk : k' ∈ keys := (Hmem k').2 (by rw [hv]; rfl)
        rw [show ((GMap.size M1 : Nat) : Int).toNat = keys.length by omega, List.take_length] at Hag
        rw [Hag k' hk, hv]
      · intro _; rfl
  · rw [decide_eq_false (fun h => hs (hw.1 h))]
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    constructor
    · intro h; cases h
    · intro h; exact absurd (congrArg GMap.size h) hs

end proof

end Perennial
