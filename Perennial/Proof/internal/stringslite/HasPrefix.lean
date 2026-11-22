/-
`internal.stringslite.HasPrefix`'s proof.
-/
module

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

theorem internal.stringslite.HasPrefix.wp_proof :
    internal.stringslite.HasPrefix.spec (GF := GF) (hG := hG) := by
  intro s pre
  wp_start
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hs
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hp
  wp_if_destruct
  · wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
    have hle : pre.length ≤ s.length := by word
    rw [ite_eq_left (by word)]
    rw [show sint.nat (W64 (pre.length : Int)) = pre.length by word]
    wp_auto
    simp only [Nat.sub_zero, List.drop_zero]
    rw [show decide (List.take pre.length s = pre) = decide (pre <+: s) by
      simp only [List.prefix_iff_eq_take, eq_comm]]
    iapply HΦ; itrivial
  · rw [decide_eq_false (fun h => by have := h.length_le; word)]
    iapply HΦ; itrivial

end proof

end Perennial
