/-
The proof of `internal.stringslite.HasSuffix`.
-/
module

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

theorem internal.stringslite.HasSuffix.wp_proof :
    internal.stringslite.HasSuffix.spec (GF := GF) (hG := hG) := by
  intro s suf
  wp_start
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hs
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hp
  wp_if_destruct
  · wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
    have hle : suf.length ≤ s.length := by word
    rw [ite_eq_left (by word)]
    rw [show sint.nat (W64 (s.length : Int)) = s.length by word,
      show sint.nat (W64 (s.length : Int) - W64 (suf.length : Int)) = s.length - suf.length by word,
      List.take_of_length_le (by simp)]
    wp_auto
    rw [show decide (List.drop (s.length - suf.length) s = suf) = decide (suf <:+ s) by
      simp only [List.suffix_iff_eq_drop, eq_comm]]
    iapply HΦ; itrivial
  · rw [decide_eq_false (fun h => by have := h.length_le; word)]
    iapply HΦ; itrivial

end proof

end Perennial
