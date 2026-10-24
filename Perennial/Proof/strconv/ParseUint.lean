/-
The proof of `strconv.ParseUint`.
-/
module

public import Perennial.Spec.strconv.ParseUint
public import Perennial.Spec.strconv.toError
public import Perennial.Spec.internal.strconv.ParseUint

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strconv.Assumptions]

theorem strconv.ParseUint.wp_proof
    (wp_ParseUint : internal.strconv.ParseUint.spec (GF := GF) (hG := hG))
    (wp_toError : strconv.toError.spec (GF := GF) (hG := hG)) :
    strconv.ParseUint.spec (GF := GF) (hG := hG) := by
  intro s base bitSize Hb1 Hb2 Hs1 Hs2
  wp_start
  wp_auto
  wp_apply wp_ParseUint s base bitSize Hb1 Hb2 Hs1 Hs2 as %x %err %Hout
  generalize internal.strconv.parseUint s (sint.nat base) (sint.nat bitSize) = r at Hout ⊢
  cases r with
  | ok n =>
    obtain ⟨rfl, rfl⟩ := Hout
    wp_auto
    iapply HΦ
    ipureintro; exact ⟨rfl, rfl⟩
  | errSyntax =>
    obtain ⟨rfl, rfl⟩ := Hout
    wp_auto
    have H := wp_toError go!"ParseUint" s base bitSize true
    simp only [ite_true] at H
    wp_apply H as %e He
    iapply HΦ
    dsimp only
    iframe He
    ipureintro; rfl
  | errRange =>
    obtain ⟨rfl, rfl⟩ := Hout
    wp_auto
    have H := wp_toError go!"ParseUint" s base bitSize false
    simp only [Bool.false_eq_true, ite_false] at H
    wp_apply H as %e He
    iapply HΦ
    dsimp only
    iframe He
    ipureintro; rfl

end proof

end Perennial
