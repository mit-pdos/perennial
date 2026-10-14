/-
The proof of `math/big.(*Int).Int64`.
-/
module

public import Perennial.Spec.math.big.Int__Int64
public import Perennial.Spec.math.big.low64

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : math.big.Assumptions]

theorem math.big.Int.Int64.wp_proof
    (wp_low64 : math.big.low64.spec (GF := GF) (hG := hG)) :
    math.big.Int.Int64.spec (GF := GF) (hG := hG) := by
  intro p z Hz
  wp_start as H
  unfold ownInt
  icases H with ⟨%x, %ws, Hp, Hws, %Hz, %Hnorm⟩
  wp_auto
  wp_apply wp_low64 $$ [Hws] with Hws
  · iexact Hws
  have Hsmall := natValue_small ws (by split at Hz <;> omega)
  generalize ws.headD (W64 0) = w at Hsmall
  wp_auto
  cases Hneg : x.neg'
  all_goals
    simp only [Hneg, Bool.false_eq_true, ↓reduceIte] at Hz ⊢
    wp_auto
  · rw [show w = W64 z by rw [Hz, Hsmall]; word]
    iapply HΦ
    iexists x, ws
    iframe
    ipureintro
    exact ⟨by simp only [Hneg, Bool.false_eq_true, ↓reduceIte, Hz], Hnorm⟩
  · rw [show -w = W64 z by rw [Hz, Hsmall]; word]
    iapply HΦ
    iexists x, ws
    iframe
    ipureintro
    exact ⟨by simp only [Hneg, ↓reduceIte, Hz], Hnorm⟩

end proof

end Perennial
