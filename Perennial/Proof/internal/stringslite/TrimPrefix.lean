/-
The proof of `internal.stringslite.TrimPrefix`.
-/
module

public import Perennial.Spec.internal.stringslite.TrimPrefix
public import Perennial.Spec.internal.stringslite.HasPrefix
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

theorem internal.stringslite.TrimPrefix.wp_proof
    (wp_HasPrefix : internal.stringslite.HasPrefix.spec (GF := GF) (hG := hG)) :
    internal.stringslite.TrimPrefix.spec (GF := GF) (hG := hG) := by
  intro s pre
  wp_start
  wp_auto
  wp_apply wp_HasPrefix
  by_cases h : pre <+: s
  · simp only [h, decide_true, ↓reduceIte]
    wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hp
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hs
    have hle : pre.length ≤ s.length := h.length_le
    rw [ite_eq_left (by word)]
    rw [show sint.nat (W64 (s.length : Int)) = s.length by word,
      show sint.nat (W64 (pre.length : Int)) = pre.length by word,
      List.take_of_length_le (by simp)]
    wp_auto
    iapply HΦ; itrivial
  · simp only [h, decide_false, ↓reduceIte]
    wp_auto
    iapply HΦ; itrivial

end proof

end Perennial
