/-
The proof of `strconv.Atoi`.
-/
module

public import Perennial.Spec.strconv.Atoi
public import Perennial.Spec.strconv.toError
public import Perennial.Spec.internal.strconv.Atoi

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

theorem strconv.Atoi.wp_proof
    (wp_Atoi : internal.strconv.Atoi.spec (GF := GF) (hG := hG))
    (wp_toError : strconv.toError.spec (GF := GF) (hG := hG)) :
    strconv.Atoi.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start
  wp_auto
  wp_apply wp_Atoi s as %x %err %Herr
  rcases Herr with rfl | rfl | rfl
  · wp_auto
    iapply HΦ
    ileft; ipureintro; rfl
  · wp_auto
    have H := wp_toError go!"Atoi" s (W64 0) (W64 0) true
    simp only [ite_true] at H
    wp_apply H as %e He
    iapply HΦ
    iright; ileft
    iexact He
  · wp_auto
    have H := wp_toError go!"Atoi" s (W64 0) (W64 0) false
    simp only [Bool.false_eq_true, ite_false] at H
    wp_apply H as %e He
    iapply HΦ
    iright; iright
    iexact He

end proof

end Perennial
