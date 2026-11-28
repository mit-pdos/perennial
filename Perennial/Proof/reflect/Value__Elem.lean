/-
The proof of `reflect.Value.Elem`.
-/
module

public import Perennial.Spec.reflect.Value__Elem
public import Perennial.Spec.reflect.flag__kind
public import Perennial.Spec.internal.reflectcore.EqNilAt
public import Perennial.Spec.internal.reflectcore.TypeElem
public import Perennial.Spec.internal.reflectcore.TypeKind
public import Perennial.Spec.internal.reflectcore.PtrTok
public import Perennial.Spec.internal.reflectcore.ConvertAt

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : reflect.Assumptions]

theorem reflect.Value.Elem.wp_proof
    (wp_flag_kind : reflect.flag.kind.spec (GF := GF) (hG := hG))
    (wp_EqNilAt : internal.reflectcore.EqNilAt.spec (GF := GF) (hG := hG))
    (wp_TypeElem : internal.reflectcore.TypeElem.spec (GF := GF) (hG := hG))
    (wp_TypeKind : internal.reflectcore.TypeKind.spec (GF := GF) (hG := hG))
    (wp_PtrTok : internal.reflectcore.PtrTok.spec (GF := GF) (hG := hG))
    (wp_ConvertAt : internal.reflectcore.ConvertAt.spec (GF := GF) (hG := hG)) :
    reflect.Value.Elem.spec (GF := GF) (hG := hG) := fun v T _ k l hk htyp hptr hkind hi => by
  haveI : go.NotInterface go.uintptr := ⟨by simp [go.uintptr]⟩
  wp_start as #Hinit
  wp_auto
  wp_method_call; wp_call
  wp_method_call; wp_call
  wp_auto
  wp_apply wp_flag_kind
  rw [hkind]
  wp_auto
  simp only [hi, decide_true, Bool.not_true]
  wp_auto
  rw [hptr]
  wp_apply wp_EqNilAt.1 (t := go.PointerType T) l
  wp_if_destruct
  · iapply HΦ
    itrivial
  · haveI : T ↓u (_root_.Perennial.underlying T) := ⟨rfl⟩
    wp_method_call; wp_call
    wp_auto
    wp_method_call; wp_call
    wp_auto
    rw [htyp]
    have he : go.typeQuery .elem (go.PointerType T) 0 = some #(go.tok T) := by
      simp [go.typeQuery, go.is_underlying, go.NotLayoutModelled.not_layout_modelled]
    unfold go.tok at he ⊢
    wp_apply wp_TypeElem (go.PointerType T) null _ he
    wp_apply wp_TypeKind k null hk
    wp_apply wp_PtrTok
    unfold go.tok
    wp_apply wp_ConvertAt.1 (t := go.PointerType T) (u := go.PointerType T) l l null rfl rfl
      (go.convertExposed_pointer T) (go.convertExposed_pointer T)
    rw [ite_eq_right Hif]
    iapply HΦ
    itrivial

end proof

end Perennial
