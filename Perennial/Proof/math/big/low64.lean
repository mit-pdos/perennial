/-
The proof of `math/big.low64`.
-/
module

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

theorem math.big.low64.wp_proof :
    math.big.low64.spec (GF := GF) (hG := hG) := by
  intro s ws dq
  wp_start as Hs
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  wp_if_destruct
  · have : ws = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [Hlen.1, Hif]; rfl
    subst this
    simp only [List.headD]
    iapply HΦ $$ Hs
  obtain ⟨w, ws', rfl⟩ : ∃ w ws', ws = w :: ws' := by
    cases ws with
    | nil => exfalso; apply Hif; simp at Hlen; word
    | cons w ws' => exact ⟨w, ws', rfl⟩
  simp only [List.length_cons] at Hlen
  have Hpos : 0 < sint.Z s.len := by
    have := Hlen.1
    have : (sint.nat s.len : Int) = sint.Z s.len := by word
    omega
  have H0 : sint.Z (W64 0) = 0 := rfl
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
  wp_apply wp_load_slice_index s (sint.Z (W64 0)) (w :: ws') dq w (by omega) $$ [Hs] with Hs
  · iframe Hs; ipureintro; rfl
  simp only [List.headD]
  iapply HΦ $$ Hs

end proof

end Perennial
