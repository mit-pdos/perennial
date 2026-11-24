/-
The proof of `errors.asAssign` (its trusted model, the semantics' `AsAssign`).
-/
module

public import Perennial.Spec.errors.asAssign

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : errors.Assumptions]

theorem errors.asAssign.wp_proof :
    errors.asAssign.spec (GF := GF) (hG := hG) := by
  intro ii l T' _ _ T _ v hT hdec htyped
  wp_start as Hl
  ihave %hl := typedPointsto_not_null $$ Hl
  have hT' : go.isInterfaceType (underlying T) = true ∨ go.typeSetContains T go.error = true := by
    rcases hT with ⟨elems, he⟩ | h
    · left; rw [he]; rfl
    · right; exact h
  haveI := go.InterfaceSemantics.as_assign_step ii T l hl hT' hdec
  wp_auto
  unfold asAssignable asStored
  unfold AsTypeTyped at htyped
  cases hI : go.isInterfaceType (underlying T)
  · simp only [hI, Bool.false_eq_true, ↓reduceIte] at htyped ⊢
    by_cases hty : ii.ty = T
    · obtain ⟨x, hx⟩ := htyped hty
      simp only [hty, ↓reduceIte, decide_true]
      rw [← hx]
      wp_pures
      wp_store
      wp_pures
      iapply HΦ
      iframe
      ipureintro
      simp
    · simp only [hty, ↓reduceIte, decide_false]
      wp_pures
      iapply HΦ
      iframe
      ipureintro
      simp
  · simp only [hI, ↓reduceIte] at htyped ⊢
    cases hts : go.typeSetContains ii.ty T
    · simp only [Bool.false_eq_true, ↓reduceIte]
      wp_pures
      iapply HΦ
      iframe
      ipureintro
      simp
    · obtain ⟨x, hx⟩ := htyped hts
      simp only [↓reduceIte]
      rw [← hx]
      wp_pures
      wp_store
      wp_pures
      iapply HΦ
      iframe
      ipureintro
      simp

end proof

end Perennial
