/-
The proof of `internal.reflectlite.isDefined`.
-/
module

public import Perennial.Spec.internal.reflectlite.isDefined
public import Perennial.Spec.internal.reflectcore.TypeIdentByName
public import Perennial.Spec.internal.reflectcore.TypeKind
public import Perennial.Spec.internal.reflectcore.TypeElem
public import Perennial.Spec.internal.reflectcore.PtrTok

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.reflectlite.Assumptions]

theorem internal.reflectlite.isDefined.wp_proof
    (wp_TypeIdentByName : internal.reflectcore.TypeIdentByName.spec (GF := GF) (hG := hG))
    (wp_TypeKind : internal.reflectcore.TypeKind.spec (GF := GF) (hG := hG))
    (wp_TypeElem : internal.reflectcore.TypeElem.spec (GF := GF) (hG := hG))
    (wp_PtrTok : internal.reflectcore.PtrTok.spec (GF := GF) (hG := hG)) :
    internal.reflectlite.isDefined.spec (GF := GF) (hG := hG) := @fun T u _ _ k hk => by
  have hU : underlying T = u := go.is_underlying
  have hptr : ∀ X, T = go.PointerType X → u = go.PointerType X := by
    intro X hTX
    have hp : underlying (go.PointerType X) = go.PointerType X :=
      go.is_underlying
    rw [← hU, hTX, hp]
  wp_start as #Hinit
  wp_auto
  unfold go.tok
  wp_apply wp_TypeIdentByName T null
  cases hid : go.identByName T
  · wp_auto
    have : internal.reflectlite.isDefinedT T = false := by
      unfold internal.reflectlite.isDefinedT
      split
      · simp [go.identByName] at hid
      · rfl
    rw [this]
    iapply HΦ
    itrivial
  · wp_auto
    wp_apply wp_TypeKind k null hk
    try rw [internal.reflectlite.kind_w8 hk]
    have hlt := internal.reflectlite.kindOf_lt hk
    by_cases h22 : k = 22
    · subst h22
      obtain ⟨e, rfl⟩ := internal.reflectlite.kindOf_22 hk rfl
      wp_auto
      wp_apply wp_TypeElem T null #(go.tok e) (by simp [go.typeQuery, hU, go.NotLayoutModelled.not_layout_modelled])
      unfold go.tok
      wp_apply wp_PtrTok e #null
      try unfold go.tok
      unfold go.identByName at hid
      split at hid
      · try wp_auto
        simp only [internal.reflectlite.isDefinedT]
        iapply HΦ
        itrivial
      · have he := hptr _ rfl
        simp only [go.GoType.PointerType.injEq] at he
        subst he
        try wp_auto
        simp only [internal.reflectlite.isDefinedT]
        iapply HΦ
        itrivial
      · cases hid
    · simp only [decide_eq_false (internal.reflectlite.kne_22 k hlt h22)]
      try wp_auto
      have : internal.reflectlite.isDefinedT T = true := by
        unfold go.identByName at hid
        split at hid
        · rfl
        · exfalso; apply h22
          have := hptr _ rfl
          subst this
          simpa [go.kindOf] using hk.symm
        · cases hid
      rw [this]
      iapply HΦ
      itrivial

end proof

end Perennial
