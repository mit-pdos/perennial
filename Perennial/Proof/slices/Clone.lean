/-
The proof of `slices.Clone`.
-/
module

public import Perennial.Spec.slices.Clone

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

theorem slices.Clone.wp_proof :
    slices.Clone.spec (GF := GF) (hG := hG) := by
  intro V _ _ Et _ S _ s dq xs
  wp_start as Hs
  wp_auto
  by_cases Hif : s = slice.nil
  · subst Hif
    simp only [decide_true]
    wp_auto
    ihave %Hlen := ownSlice_len _ _ _ $$ Hs
    have hb : xs = [] := List.eq_nil_of_length_eq_zero (by rw [Hlen.1]; rfl)
    subst hb
    iapply HΦ
    iframe Hs
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    ipureintro; simp
  · simp only [decide_eq_false Hif]
    -- step to the slice literal without unfolding it (`wp_auto` would)
    wp_pure; wp_pure; wp_pure; wp_pure; wp_pure; wp_pure
    wp_bind (App (Val (GoInstruction (CompositeLiteral S))) (Val (LiteralValueV _)))
    iapply wp_slice_literal_nonnull (V := V) (t := Et) []
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %sl_ptr %Hnn ⟨Hsl, Hsl_cap⟩
    wp_auto
    ihave %Hlen := ownSlice_len _ _ _ $$ Hs
    by_cases hx : xs = []
    · subst hx
      have hz : s.len = W64 0 := by simp at Hlen; word
      wp_bind (App (App (Val #(functions go.append [S]))
        (Val #(slice.mk sl_ptr (W64 (go.arrayLiteralSize [])) (W64 (go.arrayLiteralSize []))))) (Val #s))
      iapply wp_slice_append_fits (V := V) (t := Et) _ s _ ⟨by simp [go.arrayLiteralSize], by word⟩
        (by simp [go.arrayLiteralSize]; word)
      wp_apply wp_slice_copy_of_len_zero (V := V) (t := Et) _ s hz
      isplitl []
      · ipureintro; exact isPanic_intoVal _
      imodintro
      have he : slice.slice (slice.mk sl_ptr (W64 (go.arrayLiteralSize [])) (W64 (go.arrayLiteralSize [])))
          V (W64 0) ((slice.mk sl_ptr (W64 (go.arrayLiteralSize [])) (W64 (go.arrayLiteralSize []))).len
            + s.len) = slice.mk sl_ptr (W64 (go.arrayLiteralSize [])) (W64 (go.arrayLiteralSize [])) := by
        simp only [slice.slice, sliceIndexRef, hz, show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0]
        congr 1 <;> simp [go.arrayLiteralSize]
      rw [he]
      wp_auto
      iapply HΦ
      iframe Hs Hsl Hsl_cap
      ipureintro
      constructor
      · intro h; cases h; exact absurd rfl Hnn
      · intro h; exact absurd h Hif
    · wp_apply wp_slice_append (V := V) (t := Et) _ [] s xs dq $$ [Hsl Hsl_cap Hs]
        with %s' ⟨Hs', Hs'_cap, Hs⟩
      · iframe Hsl Hsl_cap Hs
      rw [List.nil_append]
      ihave %Hlen' := ownSlice_len _ _ _ $$ Hs'
      iapply HΦ
      iframe Hs' Hs'_cap Hs
      ipureintro
      constructor
      · intro h; subst h; exfalso; apply hx
        exact List.eq_nil_of_length_eq_zero (by rw [Hlen'.1]; rfl)
      · intro h; exact absurd h Hif

end proof

end Perennial
