/-
The proof of `crypto/sha1.(*digest).Reset`.
-/
module

public import Perennial.Spec.crypto.sha1.digest__Reset

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.sha1.Assumptions]

theorem crypto.sha1.digest.Reset.wp_proof :
    crypto.sha1.digest.Reset.spec (GF := GF) (hG := hG) := by
  intro d v
  wp_start as Hd
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hd
  obtain ⟨⟨harr⟩, x, nx, len⟩ := v
  ihave %Hhl := array_len _ _ _ _ $$ [Hd]
  · iStructNamed Hd
    iexact h
  iStructNamed Hd
  wp_auto
  obtain ⟨a0, a1, a2, a3, a4, rfl⟩ : ∃ a0 a1 a2 a3 a4, harr = [a0, a1, a2, a3, a4] := by
    match harr, Hhl with
    | [a0, a1, a2, a3, a4], _ => exact ⟨a0, a1, a2, a3, a4, rfl⟩
  icases array_acc (V := w32) _ (sint.Z (W64 0)) _ _ _ a0 (by decide)
    (by simp (disch := decide) only [encoding.binary.sint_W64_lit]; simp) $$ h with ⟨He, h⟩
  wp_auto
  ihave h := h $$ %_ He
  simp (disch := decide) only [encoding.binary.sint_W64_lit, Int.reduceToNat, List.set_cons_zero,
    List.set_cons_succ]
  icases array_acc (V := w32) _ 1 _ _ _ a1 (by decide) (by simp) $$ h with ⟨He, h⟩
  wp_auto
  ihave h := h $$ %_ He
  simp (disch := decide) only [encoding.binary.sint_W64_lit, Int.reduceToNat, List.set_cons_zero,
    List.set_cons_succ]
  icases array_acc (V := w32) _ 2 _ _ _ a2 (by decide) (by simp) $$ h with ⟨He, h⟩
  wp_auto
  ihave h := h $$ %_ He
  simp (disch := decide) only [encoding.binary.sint_W64_lit, Int.reduceToNat, List.set_cons_zero,
    List.set_cons_succ]
  icases array_acc (V := w32) _ 3 _ _ _ a3 (by decide) (by simp) $$ h with ⟨He, h⟩
  wp_auto
  ihave h := h $$ %_ He
  simp (disch := decide) only [encoding.binary.sint_W64_lit, Int.reduceToNat, List.set_cons_zero,
    List.set_cons_succ]
  icases array_acc (V := w32) _ 4 _ _ _ a4 (by decide) (by simp) $$ h with ⟨He, h⟩
  wp_auto
  ihave h := h $$ %_ He
  simp (disch := decide) only [encoding.binary.sint_W64_lit, Int.reduceToNat, List.set_cons_zero,
    List.set_cons_succ]
  iapply HΦ
  iexists ⟨array.mk 5 [W32 1732584193, W32 4023233417, W32 2562383102, W32 271733878, W32 3285377520],
    x, W64 0, W64 0⟩
  isplitl
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ipureintro
  refine ⟨⟨⟨?_, rfl, by simp⟩, rfl⟩, rfl⟩
  rw [crypto.sha1.compressAll_short _ _ (by simp)]
  rfl

end proof

end Perennial
