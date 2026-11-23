/-
The proof of `maps.Values`: as `maps.Keys`'s, the closure it returns runs Perennial's `for range`
rule over the read-only map (`wp_map_for_range`), calling yield on the value of each key; the list
yielded is the keys' values, in the keys' order (`valuesOf`).
-/
module

public import Perennial.Spec.maps.Values

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

theorem maps.Values.wp_proof : maps.Values.spec (GF := GF) (hG := hG) := by
  intro K V _ _ _ _ _ T Kt Vt _ _ _ _ _
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
        □ (∀ (j : Nat) (x : V), ⌜(keys.map fun k => (M !! k).getD (zero_val V))[j]? = some x⌝ -∗
          I j -∗
          WP (App (Val #yield) (Val #x)) {{ r, ∃ b : Bool, ⌜r = #b⌝ ∗
            (if b then I (j + 1) else (m ↦${dq} M -∗ Φ' #())) }}) ∗
        (I keys.length -∗ m ↦${dq} M -∗ Φ' #()) ∗
        (∃ vv : V, v_ptr ↦ vv) ∗
        ⌜0 ≤ i⌝))) $$ HM
    iintro %keys %Hkeys
    obtain ⟨Hmem, Hsize, Hnd⟩ := Hkeys
    have hF : List.Forall₂ (fun k v => M !! k = some v) keys
        (keys.map fun k => (M !! k).getD (zero_val V)) := by
      have hall : ∀ k ∈ keys, (M !! k).isSome := fun k hk => (Hmem k).1 hk
      clear Hmem Hsize Hnd
      induction keys with
      | nil => exact List.Forall₂.nil
      | cons a t ih =>
        refine List.Forall₂.cons ?_ (ih fun k hk => hall k (List.mem_cons_of_mem _ hk))
        have := hall a (List.mem_cons_self ..)
        cases h : M !! a <;> simp_all
    icases HY $$ %(keys.map fun k => (M !! k).getD (zero_val V)) %(⟨keys, ⟨Hmem, Hnd⟩, hF⟩)
      with ⟨%I, HI, #Hy, Hfin⟩
    simp only [List.length_map]
    isplitl [HI Hfin v]
    · iexists I
      simp only [Int.toNat_zero]
      iframe HI Hfin
      isplitr
      · iexact Hy
      isplitl [v]
      · iexists _; iframe
      ipureintro; omega
    isplitr
    · imodintro
      iintro %i %key %vl ⟨%Hk, %Hlook⟩ ⟨%I', HI, #Hy', Hfin, ⟨%vv, v⟩, %Hi⟩
      wp_auto
      have Hk' : (keys.map fun k => (M !! k).getD (zero_val V))[i.toNat]? = some vl := by
        simp [List.getElem?_map, Hk, Hlook]
      wp_bind (App (Val #yield) (Val #vl))
      iapply wp_wand $$ (Hy' $$ %(i.toNat) %vl %Hk' HI)
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
        isplitl [v]
        · iexists _; iframe
        ipureintro; omega
    · iintro ⟨%I', HI, #Hy', Hfin, v, %Hi⟩ HM
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
    icases HY $$ %([] : List V) %rfl with ⟨%I, HI, -, Hfin⟩
    rw [recv_eq_func_mk]
    wp_auto
    iapply Hfin $$ HI HR

end proof

end Perennial
