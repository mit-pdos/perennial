/-
The proof of `internal.bytealg.IndexString`.
-/
module

public import Perennial.Spec.internal.bytealg.IndexString
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

/-- Proved from the model of `IndexString` (`Perennial/TrustedCode/internal/bytealg.lean`). -/
theorem internal.bytealg.IndexString.wp_proof :
    internal.bytealg.IndexString.spec (GF := GF) (hG := hG) := fun a b m Hb => by
  wp_start as #HM
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hblen
  unfold MaxLenAddr
  rw [show (go!"internal/bytealg.MaxLen" : GoString) = MaxLen from rfl,
    decide_eq_false (show ¬ sint.Z (W64 b.length) < sint.Z (W64 2) by word)]
  wp_auto
  rw [decide_eq_false (show ¬ sint.Z m < sint.Z (W64 b.length) by word)]
  wp_auto
  have H0 : 0 ≤ sint.Z (W64 0) ∧ ∀ j, j < sint.nat (W64 0) → ¬ b <+: a.drop j :=
    ⟨by decide, fun j hj => by simp at hj; omega⟩
  generalize W64 0 = i at H0 ⊢
  iloeb as IH generalizing %i %H0
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Ha
  have Hsub : sint.Z (W64 a.length - W64 b.length) = a.length - b.length := by word
  wp_if_destruct
  · rw [Hsub] at Hif
    have Hk : 0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z (i + W64 b.length) ∧
        sint.Z (i + W64 b.length) ≤ a.length := by word
    rw [ite_eq_left Hk]
    wp_auto
    have Hlen : sint.nat (i + W64 b.length) - sint.nat i = b.length := by word
    rw [Hlen]
    wp_if_destruct
    · rw [← indexResult_of_occ a b i H0.1 (by word) ((slice_eq_iff_occ _ _ _).1 Hif) H0.2]
      iapply HΦ; itrivial
    · have H1 : 0 ≤ sint.Z (i + W64 1) ∧
          ∀ j, j < sint.nat (i + W64 1) → ¬ b <+: a.drop j := by
        refine ⟨by word, fun j hj => ?_⟩
        rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word] at hj
        rcases Nat.lt_or_ge j (sint.nat i) with hj' | hj'
        · exact H0.2 j hj'
        · obtain rfl : j = sint.nat i := by omega
          rw [← slice_eq_iff_occ]; exact Hif
      iapply IH $$ %(i + W64 1) %H1 HΦ
  · rw [Hsub] at Hif
    rw [indexResult_of_none a b ?_]
    · iapply HΦ; itrivial
    intro j hj
    rcases Nat.lt_or_ge j (sint.nat i) with hj' | hj'
    · exact H0.2 j hj'
    · exact not_occ_of_short a b (by rintro rfl; simp at Hb) j (by word)

end proof

end Perennial
