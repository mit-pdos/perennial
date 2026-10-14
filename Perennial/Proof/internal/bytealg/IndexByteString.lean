/-
The proof of `internal.bytealg.IndexByteString`.
-/
module

public import Perennial.Spec.internal.bytealg.IndexByteString
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

/-- Proved from the model of `IndexByteString` (`Perennial/TrustedCode/internal/bytealg.lean`). -/
theorem internal.bytealg.IndexByteString.wp_proof :
    internal.bytealg.IndexByteString.spec (GF := GF) (hG := hG) := fun s c => by
  wp_start
  have H0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ s.length ∧
      ∀ j, j < sint.nat (W64 0) → ¬ [c] <+: s.drop j :=
    ⟨by decide, by word, fun j hj => by simp at hj; omega⟩
  generalize W64 0 = i at H0 ⊢
  iloeb as IH generalizing %i %H0
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hs
  wp_if_destruct
  · have hlt : sint.nat i < s.length := by word
    obtain ⟨b, hb⟩ : ∃ b, s[sint.nat i]? = some b := ⟨_, List.getElem?_eq_getElem hlt⟩
    simp only [H0.1, ↓reduceIte, hb]
    wp_auto
    wp_if_destruct
    · subst Hif
      rw [← indexResult_of_occ s [b] i H0.1 (by omega) ((occ_singleton_iff _ _ _).2 hb) H0.2.2]
      iapply HΦ; itrivial
    · have H1 : 0 ≤ sint.Z (i + W64 1) ∧ sint.Z (i + W64 1) ≤ s.length ∧
          ∀ j, j < sint.nat (i + W64 1) → ¬ [c] <+: s.drop j := by
        refine ⟨by word, by word, fun j hj => ?_⟩
        rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word] at hj
        rcases Nat.lt_or_ge j (sint.nat i) with hj' | hj'
        · exact H0.2.2 j hj'
        · obtain rfl : j = sint.nat i := by omega
          rw [occ_singleton_iff, hb]
          intro h; cases h; exact Hif rfl
      iapply IH $$ %(i + W64 1) %H1 HΦ
  · rw [indexResult_of_none s [c] ?_]
    · iapply HΦ; itrivial
    intro j hj
    rcases Nat.lt_or_ge j (sint.nat i) with hj' | hj'
    · exact H0.2.2 j hj'
    · exact not_occ_of_short s [c] (by simp) j (by simp; word)

end proof

end Perennial
