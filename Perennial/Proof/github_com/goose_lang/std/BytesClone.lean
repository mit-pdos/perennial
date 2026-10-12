/-
The proof of `github.com/goose-lang/std.BytesClone`.
-/
module

public import Perennial.Spec.github_com.goose_lang.std.BytesClone

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.goose_lang.std.Assumptions]

theorem github_com.goose_lang.std.BytesClone.wp_proof :
    github_com.goose_lang.std.BytesClone.spec (GF := GF) (hG := hG) := fun b xs dq => by
  wp_start as Hb
  wp_auto
  by_cases Hif : b = slice.nil
  · subst Hif
    simp only [_root_.decide_true]
    wp_auto
    ihave %Hlen := ownSlice_len _ _ _ $$ Hb
    have hb : xs = [] := List.eq_nil_of_length_eq_zero (by rw [Hlen.1]; rfl)
    subst hb
    iapply HΦ
    isplitl []
    · iapply ownSlice_nil
    · iapply ownSliceCap_nil
  · simp only [decide_eq_false Hif]
    wp_pure; wp_pure; wp_pure; wp_pure; wp_pure; wp_pure
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte)))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w8) (t := go.byte) []
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %sl_ptr ⟨Hsl, Hsl_cap⟩
    wp_auto
    wp_apply wp_slice_append (V := w8) (t := go.byte) _ [] b xs dq $$ [Hsl Hsl_cap Hb]
      with %s' ⟨Hs', Hs'_cap, Hb⟩
    · iframe Hsl Hsl_cap Hb
    rw [List.nil_append]
    iapply HΦ
    iframe Hs' Hs'_cap

end proof

end Perennial
