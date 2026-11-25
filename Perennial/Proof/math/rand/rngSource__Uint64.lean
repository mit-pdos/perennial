/-
The proof of `math/rand.rngSource.Uint64`.
-/
module

public import Perennial.Spec.math.rand.rngSource__Uint64

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace math.rand

/-- An index of `rngSource` after `Uint64`'s decrement and wrap (`tap--; if tap < 0 { tap +=
rngLen }`). -/
def nextIdx (t : w64) : w64 :=
  if sint.Z (t - W64 1) < sint.Z (W64 0) then t - W64 1 + W64 607 else t - W64 1

theorem nextIdx_neg (t : w64) (h : sint.Z (t - W64 1) < sint.Z (W64 0)) :
    t - W64 1 + W64 607 = nextIdx t := by
  unfold nextIdx; rw [ite_eq_left h]

theorem nextIdx_nonneg (t : w64) (h : ¬sint.Z (t - W64 1) < sint.Z (W64 0)) :
    t - W64 1 = nextIdx t := by
  unfold nextIdx; rw [ite_eq_right h]

theorem nextIdx_bounds (t : w64) (h0 : 0 ≤ sint.Z t) (h1 : sint.Z t < 607) :
    0 ≤ sint.Z (nextIdx t) ∧ sint.Z (nextIdx t) < 607 := by
  unfold nextIdx
  split <;> constructor <;> word

end math.rand

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.rand.Assumptions]

theorem math.rand.rngSource.Uint64.wp_proof :
    math.rand.rngSource.Uint64.spec (GF := GF) (hG := hG) := by
  intro p
  wp_start as Hp
  iunfold math.rand.ownRngSource at Hp
  icases Hp with ⟨%v, Hp, %Hok⟩
  wp_auto
  obtain ⟨Ht0, Ht1, Hf0, Hf1, Hlen⟩ := Hok
  wp_if_destruct <;>
    first
    | rw [math.rand.nextIdx_neg v.tap' (by assumption)]
    | rw [math.rand.nextIdx_nonneg v.tap' (by assumption)]
  all_goals
    wp_if_destruct <;>
      first
      | rw [math.rand.nextIdx_neg v.feed' (by assumption)]
      | rw [math.rand.nextIdx_nonneg v.feed' (by assumption)]
  all_goals
    have hT := math.rand.nextIdx_bounds v.tap' Ht0 Ht1
    have hF := math.rand.nextIdx_bounds v.feed' Hf0 Hf1
    icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hnn⟩
    iStructNamed Hp
    try wp_auto
    rw [ite_eq_left hF]
    obtain ⟨xf, hxf⟩ : ∃ x, v.vec'.arr[(sint.Z (nextIdx v.feed')).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨xt, hxt⟩ : ∃ x, v.vec'.arr[(sint.Z (nextIdx v.tap')).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    icases array_acc (V := w64) _ (sint.Z (nextIdx v.feed')) _ 607 v.vec' xf hF.1 hxf $$ vec
      with ⟨Hel, Hclose⟩
    try wp_auto
    ihave vec := Hclose $$ %xf Hel
    rw [list_set_getElem?_self _ _ _ hxf]
    rw [ite_eq_left hT]
    icases array_acc (V := w64) _ (sint.Z (nextIdx v.tap')) _ 607 (array.mk 607 v.vec'.arr) xt
      hT.1 hxt $$ vec with ⟨Hel, Hclose⟩
    try wp_auto
    ihave vec := Hclose $$ %xt Hel
    rw [list_set_getElem?_self _ _ _ hxt]
    rw [ite_eq_left hF]
    icases array_acc (V := w64) _ (sint.Z (nextIdx v.feed')) _ 607 (array.mk 607 v.vec'.arr) xf
      hF.1 hxf $$ vec with ⟨Hel, Hclose⟩
    try wp_auto
    ihave vec := Hclose $$ %(xf + xt) Hel
    try wp_auto
    iapply HΦ
    iunfold math.rand.ownRngSource
    iexists (math.rand.rngSource.mk (nextIdx v.tap') (nextIdx v.feed')
      (array.mk 607 (v.vec'.arr.set (sint.Z (nextIdx v.feed')).toNat (xf + xt))))
    isplitl [tap feed vec]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    · ipureintro
      unfold math.rand.rngSourceOk
      simp only [List.length_set, Hlen]
      exact ⟨hT.1, hT.2, hF.1, hF.2, trivial⟩

end proof

end Perennial
