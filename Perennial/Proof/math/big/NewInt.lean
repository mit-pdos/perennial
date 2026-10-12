/-
The proof of `math/big.NewInt`.
-/
module

public import Perennial.Spec.math.big.NewInt

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.big.Assumptions]

theorem math.big.NewInt.wp_proof :
    math.big.NewInt.spec (GF := GF) (hG := hG) := by
  intro v
  wp_start
  wp_auto
  wp_if_destruct
  · wp_if_destruct
    · exfalso; revert ‹sint.Z (W64 0) < _›; decide
    wp_apply wp_slice_literal (V := w64) [-v]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    wp_alloc p as Hp
    wp_auto
    iapply HΦ
    unfold ownInt
    iexists _, [-v]
    iframe
    ipureintro
    refine ⟨?_, ?_⟩
    · simp only [decide_eq_true ‹sint.Z v < sint.Z (W64 0)›, ↓reduceIte, natValue]
      word
    · simp only [natNormalized, List.getLast?_singleton, ne_eq, Option.some.injEq]
      intro h
      have : sint.Z v < 0 := ‹sint.Z v < sint.Z (W64 0)›
      have : v = W64 0 := by rw [show v = - -v by simp, h]; rfl
      subst this; simp at *
  · wp_if_destruct
    · wp_alloc p as Hp
      wp_auto
      iapply HΦ
      unfold ownInt
      iexists _, []
      iframe
      isplitl
      · iapply ownSlice_nil
      ipureintro
      simp [natValue, natNormalized]
    wp_apply wp_slice_literal (V := w64) [v]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    wp_alloc p as Hp
    wp_auto
    iapply HΦ
    unfold ownInt
    iexists _, [v]
    iframe
    ipureintro
    refine ⟨?_, ?_⟩
    · simp only [decide_eq_false ‹¬sint.Z v < sint.Z (W64 0)›, Bool.false_eq_true, ↓reduceIte,
        natValue]
      word
    · simp only [natNormalized, List.getLast?_singleton, ne_eq, Option.some.injEq]
      exact ‹¬v = W64 0›

end proof

end Perennial
