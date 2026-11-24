/-
The proof of `internal.stringslite.Cut`.
-/
module

public import Perennial.Spec.internal.stringslite.Cut
public import Perennial.Spec.internal.stringslite.Index
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

theorem internal.stringslite.Cut.wp_proof
    (wp_Index : internal.stringslite.Index.spec (GF := GF) (hG := hG)) :
    internal.stringslite.Cut.spec (GF := GF) (hG := hG) := by
  intro s sep
  wp_start as #Hinit
  wp_auto
  wp_apply wp_Index as %Hsl
  rcases internal.bytealg.index_cases s sep with ⟨i, hi, hp, hmin⟩ | ⟨hi, -⟩
  · have hb := (internal.bytealg.index_bounds s sep).2 (by omega)
    rw [hi] at hb ⊢
    have Hsl' : i = 0 ∨ s.length < 2 ^ 63 := by
      rcases Nat.eq_zero_or_pos i with h | h
      · exact Or.inl h
      · refine Or.inr (Hsl fun hn => hmin 0 h ?_)
        rw [hn]; exact List.nil_prefix
    have Hi63 : i < 2 ^ 63 := by omega
    wp_if_destruct
    · try wp_auto
      rw [ite_eq_left (by word)]
      try wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hsl2
      try wp_auto
      rw [ite_eq_left (by word)]
      try wp_auto
      have hcut : internal.stringslite.cut s sep =
          (s.take i, s.drop (i + sep.length), true) := by
        simp [internal.stringslite.cut, hi]
      rw [hcut]
      rw [show sint.nat (W64 (i : Int)) = i by word,
        show sint.nat (W64 (i : Int) + W64 (sep.length : Int)) = i + sep.length by word,
        show sint.nat (W64 (s.length : Int)) - (i + sep.length) = s.length - (i + sep.length)
          by word]
      simp only [Nat.sub_zero, List.drop_zero]
      rw [show List.take (s.length - (i + sep.length)) (List.drop (i + sep.length) s) =
        List.drop (i + sep.length) s from List.take_of_length_le (by simp)]
      iapply HΦ
      itrivial
    · exfalso; revert Hif; word
  · rw [hi]
    wp_if_destruct
    · exfalso; revert Hif; word
    try wp_auto
    have hcut : internal.stringslite.cut s sep = (s, [], false) := by
      simp [internal.stringslite.cut, hi]
    rw [hcut]
    iapply HΦ
    itrivial

end proof

end Perennial
