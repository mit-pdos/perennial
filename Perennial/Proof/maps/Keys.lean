/-
The proof of `maps.Keys`: the closure it returns runs Perennial's `for range` rule over the
read-only map (`wp_map_for_range`), calling yield on each key.
-/
module

public import Perennial.Spec.maps.Keys

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

theorem maps.Keys.wp_proof : maps.Keys.spec (GF := GF) (hG := hG) := by
  intro K V _ _ _ _ _ T Kt Vt _ _ _
  constructor
  · intro m
    wp_start
    wp_alloc_auto
    wp_pures
    wp_alloc_auto
    ipersist m
    wp_auto
    iapply HΦ
    imodintro
    iintro %dq %M
    unfold iter.SeqRuns
    iintro %yield %Φ' HM HY
    wp_pures
    wp_alloc_auto
    ipersist yield
    wp_auto
    wp_apply (wp_map_for_range (fun keys i => iprop(∃ I : Nat → IProp GF,
        I i.toNat ∗
        □ (∀ (j : Nat) (x : K), ⌜keys[j]? = some x⌝ -∗ I j -∗
          WP (App (Val #yield) (Val #x)) {{ r, ∃ b : Bool, ⌜r = #b⌝ ∗
            (if b then I (j + 1) else (m ↦${dq} M -∗ Φ' #())) }}) ∗
        (I keys.length -∗ m ↦${dq} M -∗ Φ' #()) ∗
        (∃ kv : K, k_ptr ↦ kv) ∗
        ⌜0 ≤ i⌝))) $$ HM
    iintro %keys %Hkeys
    obtain ⟨Hmem, Hsize, Hnd⟩ := Hkeys
    icases HY $$ %keys %(⟨Hmem, Hnd⟩) with ⟨%I, HI, #Hy, Hfin⟩
    isplitl [HI Hfin k]
    · iexists I
      simp only [Int.toNat_zero]
      iframe HI Hfin
      isplitr
      · iexact Hy
      isplitl [k]
      · iexists _; iframe
      ipureintro; omega
    isplitr
    · imodintro
      iintro %i %key %v ⟨%Hk, %Hlook⟩ ⟨%I', HI, #Hy', Hfin, ⟨%kv, k⟩, %Hi⟩
      wp_auto
      wp_bind (App (Val #yield) (Val #key))
      iapply wp_wand $$ (Hy' $$ %(i.toNat) %key %Hk HI)
      iintro %r ⟨%b, %hr, Hb⟩
      subst hr
      unfold forMapPostcondition
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        wp_auto
        iright; iright; iright; ileft
        iexists #()
        isplitr
        · ipureintro; rfl
        iintro HM
        wp_auto
        iapply Hb $$ HM
      · simp only [↓reduceIte]
        wp_auto
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists I'
        rw [show (i + 1).toNat = i.toNat + 1 by omega]
        iframe Hb Hfin
        isplitr
        · iexact Hy'
        isplitl [k]
        · iexists _; iframe
        ipureintro; omega
    · iintro ⟨%I', HI, #Hy', Hfin, k, %Hi⟩ HM
      rw [show ((GMap.size M : Nat) : Int).toNat = keys.length by omega]
      wp_auto
      iapply Hfin $$ HI HM
  · wp_start
    wp_alloc_auto
    wp_pures
    wp_alloc_auto
    ipersist m
    wp_auto
    iapply HΦ
    imodintro
    unfold iter.SeqRuns
    iintro %yield %Φ' HR HY
    wp_pures
    wp_alloc_auto
    ipersist yield
    wp_auto
    icases HY $$ %([] : List K) %rfl with ⟨%I, HI, -, Hfin⟩
    rw [recv_eq_func_mk]
    wp_auto
    iapply Hfin $$ HI HR

end proof

end Perennial
