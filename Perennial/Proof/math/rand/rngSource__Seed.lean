/-
The proof of `math/rand.rngSource.Seed`.
-/
module

public import Perennial.Spec.math.rand.rngSource__Seed
public import Perennial.Spec.math.rand.seedrand

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.rand.Assumptions]

theorem math.rand.rngSource.Seed.wp_proof
    (wp_seedrand : math.rand.seedrand.spec (GF := GF) (hG := hG)) :
    math.rand.rngSource.Seed.spec (GF := GF) (hG := hG) := by
  intro p v seed
  wp_start as Hp
  ihave #Hi := math.rand.isInit_access $$ Hpkg
  iunfold math.rand.isInit at Hi
  icases Hi with ⟨-, %a, #Hcooked⟩
  obtain ⟨cs⟩ := a
  ihave %Hclen := array_len _ _ _ _ $$ Hcooked
  obtain ⟨t0, f0, ⟨vs0⟩⟩ := v
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hnn⟩
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨tap, feed, vec, -⟩
  icases persistent_entails_left (array_len _ _ _ _) $$ vec with ⟨vec, %Hvlen⟩
  wp_auto
  wp_if_destruct <;> (try wp_auto)
  all_goals wp_if_destruct <;> (try wp_auto)
  all_goals
    ihave IH : iprop(∃ (j : w64) (y : w32) (vs : List w64), "i" ∷ i_ptr ↦ j ∗ "x" ∷ x_ptr ↦ y ∗
        "vec" ∷ structFieldRef math.rand.rngSource go!"vec" p ↦ (array.mk 607 vs : GoArray w64 607) ∗
        "%Hj" ∷ ⌜-20 ≤ sint.Z j ∧ sint.Z j ≤ 607 ∧ vs.length = 607⌝) $$ [i x vec]
    · iexists _, _, vs0
      iframe
      ipureintro
      refine ⟨by word, by word, by omega⟩
    wp_for IH
    wp_if_destruct
    · try simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif
      have hj1 : sint.Z j < 607 := by word
      wp_apply wp_seedrand as %x1 -
      wp_if_destruct
      · wp_apply wp_seedrand as %x2 -
        wp_apply wp_seedrand as %x3 -
        have hj0 : 0 ≤ sint.Z j := by word
        rw [ite_eq_left ⟨hj0, hj1⟩]
        obtain ⟨c, hc⟩ : ∃ c, cs[(sint.Z j).toNat]? = some c :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        icases array_acc (V := w64) _ (sint.Z j) _ 607 (array.mk 607 cs) c hj0 hc $$ Hcooked
          with ⟨Hc, -⟩
        try wp_auto
        rw [ite_eq_left ⟨hj0, hj1⟩]
        obtain ⟨d, hd⟩ : ∃ d, vs[(sint.Z j).toNat]? = some d :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        icases array_acc (V := w64) _ (sint.Z j) _ 607 (array.mk 607 vs) d hj0 hd $$ vec
          with ⟨Hel, Hclose⟩
        try wp_auto
        ihave vec := Hclose $$ %_ Hel
        wp_for_post
        iframe
        iexists j + W64 1, _, _
        iframe
        ipureintro
        refine ⟨by word, by word, by simp [Hj.2.2]⟩
      · wp_for_post
        iframe
        iexists j + W64 1, _, _
        iframe
        ipureintro
        refine ⟨by word, by word, Hj.2.2⟩
    · try wp_auto
      iapply HΦ
      iunfold math.rand.ownRngSource
      iexists (math.rand.rngSource.mk (W64 0) (W64 334) (array.mk 607 vs))
      isplitl [tap feed vec]
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      · ipureintro
        unfold math.rand.rngSourceOk
        exact ⟨by word, by word, by word, by word, Hj.2.2⟩

end proof

end Perennial
