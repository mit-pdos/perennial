/-
The proof of `internal.reflectlite.elem`.
-/
module

public import Perennial.Spec.internal.reflectlite.elem
public import Perennial.Spec.internal.reflectcore.TypeKind
public import Perennial.Spec.internal.reflectcore.TypeElem

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

theorem internal.reflectlite.elem.wp_proof
    (wp_TypeKind : internal.reflectcore.TypeKind.spec (GF := GF) (hG := hG))
    (wp_TypeElem : internal.reflectcore.TypeElem.spec (GF := GF) (hG := hG)) :
    internal.reflectlite.elem.spec (GF := GF) (hG := hG) := @fun T u hu e l h => by
  obtain ⟨k, hk, hk'⟩ : ∃ k, go.kindOf u = some k ∧
      (k = 17 ∨ k = 18 ∨ k = 21 ∨ k = 22 ∨ k = 23) := by
    have hu' := hu.is_underlying
    unfold go.typeQuery at h
    rw [hu'] at h
    cases u <;> simp_all [go.kindOf]
  wp_start as #Hinit
  wp_auto
  wp_apply wp_TypeKind k l hk
  rcases hk' with rfl | rfl | rfl | rfl | rfl <;>
  · wp_auto
    wp_apply wp_TypeElem T l _ h
    iapply HΦ
    itrivial

end proof

end Perennial
