/-
The proof of `strconv.ParseBool`.
-/
module

public import Perennial.Spec.strconv.ParseBool
public import Perennial.Spec.internal.strconv.ParseBool
public import Perennial.Spec.strconv.toError

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strconv.Assumptions]

theorem strconv.ParseBool.wp_proof
    (wp_ParseBool : internal.strconv.ParseBool.spec (GF := GF) (hG := hG))
    (wp_toError : strconv.toError.spec (GF := GF) (hG := hG)) :
    strconv.ParseBool.spec (GF := GF) (hG := hG) := by
  intro str
  wp_start
  wp_auto
  wp_apply wp_ParseBool as %b %err %H
  rcases hp : internal.strconv.parseBool str with _ | b'
  · rw [hp] at H
    obtain ⟨rfl, rfl⟩ := H
    wp_auto
    have h := wp_toError go!"ParseBool" str (W64 0) (W64 0) true
    simp only [↓reduceIte] at h
    wp_apply h as %e He
    iapply HΦ
    isplitr
    · ipureintro; trivial
    · iexact He
  · rw [hp] at H
    obtain ⟨rfl, rfl⟩ := H
    wp_auto
    iapply HΦ
    ipureintro; simp

end proof

end Perennial
