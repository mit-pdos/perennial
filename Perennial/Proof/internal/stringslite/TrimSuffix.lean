/-
The proof of `internal.stringslite.TrimSuffix`.
-/
module

public import Perennial.Spec.internal.stringslite.TrimSuffix
public import Perennial.Spec.internal.stringslite.HasSuffix
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.stringslite.Assumptions]

theorem internal.stringslite.TrimSuffix.wp_proof
    (wp_HasSuffix : internal.stringslite.HasSuffix.spec (GF := GF) (hG := hG)) :
    internal.stringslite.TrimSuffix.spec (GF := GF) (hG := hG) := by
  intro s suf
  wp_start
  wp_auto
  wp_apply wp_HasSuffix
  by_cases h : suf <:+ s
  · simp only [h, decide_true, ↓reduceIte]
    wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hs
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hp
    have hle : suf.length ≤ s.length := h.length_le
    rw [ite_eq_left (by word)]
    rw [show sint.nat (W64 (s.length : Int) - W64 (suf.length : Int)) = s.length - suf.length by word,
      List.drop_zero, Nat.sub_zero]
    wp_auto
    iapply HΦ; itrivial
  · simp only [h, decide_false, ↓reduceIte]
    wp_auto
    iapply HΦ; itrivial

end proof

end Perennial
