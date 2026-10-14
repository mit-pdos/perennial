/-
The proof of `bytes.Clone`.
-/
module

public import Perennial.Spec.bytes.Clone

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : bytes.Assumptions]

theorem bytes.Clone.wp_proof :
    bytes.Clone.spec (GF := GF) (hG := hG) := by
  intro sl_b dq b
  wp_start
  iNamed Hpre
  wp_auto
  by_cases Hif : sl_b = slice.nil
  · subst Hif
    simp only [decide_true]
    wp_auto
    ihave %Hlen := ownSlice_len _ _ _ $$ Hsl_b
    have hb : b = [] := List.eq_nil_of_length_eq_zero (by rw [Hlen.1]; rfl)
    subst hb
    iapply HΦ
    iframe Hsl_b
    isplitl []
    · iapply ownSlice_nil
    · iapply ownSliceCap_nil
  · simp only [decide_eq_false Hif]
    -- step to the slice literal without unfolding it (`wp_auto` would)
    wp_pure; wp_pure; wp_pure; wp_pure; wp_pure; wp_pure
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte)))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w8) (t := go.byte) []
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %sl_ptr ⟨Hsl, Hsl_cap⟩
    wp_auto
    wp_apply wp_slice_append (V := w8) (t := go.byte) _ [] sl_b b dq $$ [Hsl Hsl_cap Hsl_b]
      with %s' ⟨Hs', Hs'_cap, Hsl_b⟩
    · iframe Hsl Hsl_cap Hsl_b
    rw [List.nil_append]
    iapply HΦ
    iframe Hs' Hs'_cap Hsl_b

end proof

end Perennial
