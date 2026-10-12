/-
The proof of `internal.bytealg.CountString`.
-/
module

public import Perennial.Spec.internal.bytealg.CountString
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

/-- `CountString.loop s c i n`, for `n` the number of `c`s in `s[:i]`: the number of `c`s in
`s`. -/
theorem internal.bytealg.CountString.wp_loop (s : GoString) (c : w8) (i n : w64)
    (H : 0 ≤ sint.Z i ∧ sint.Z i ≤ s.length ∧ n = W64 ((s.take (sint.nat i)).count c)) :
    {{ (True : IProp GF) }}
      (App (App (App (App (Val CountString.loop) (Val #s)) (Val #c)) (Val #i)) (Val #n))
    {{ RET #(W64 (s.count c)); True }} := by
  iintro %Φ _ HΦ
  wp_call
  iloeb as IH generalizing %i %n %H
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hs
  wp_if_destruct
  · have hlt : sint.nat i < s.length := by word
    obtain ⟨b, hb⟩ : ∃ b, s[sint.nat i]? = some b := ⟨_, List.getElem?_eq_getElem hlt⟩
    simp only [H.1, ↓reduceIte, hb]
    wp_auto
    have Htake : s.take (sint.nat (i + W64 1)) = s.take (sint.nat i) ++ [b] := by
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, List.take_add_one, hb]; rfl
    wp_if_destruct
    · subst Hif
      have H1 : 0 ≤ sint.Z (i + W64 1) ∧ sint.Z (i + W64 1) ≤ s.length ∧
          n + W64 1 = W64 ((s.take (sint.nat (i + W64 1))).count b) := by
        refine ⟨by word, by word, ?_⟩
        rw [Htake, List.count_append, H.2.2]; simp; word
      wp_call
      iapply IH $$ %(i + W64 1) %(n + W64 1) %H1 [] HΦ
      itrivial
    · have H1 : 0 ≤ sint.Z (i + W64 1) ∧ sint.Z (i + W64 1) ≤ s.length ∧
          n = W64 ((s.take (sint.nat (i + W64 1))).count c) := by
        refine ⟨by word, by word, ?_⟩
        rw [Htake, List.count_append, H.2.2]
        simp [Hif]
      wp_call
      iapply IH $$ %(i + W64 1) %n %H1 [] HΦ
      itrivial
  · rw [H.2.2, show sint.nat i = s.length by word, List.take_length]
    iapply HΦ; itrivial


/-- Proved from the model of `CountString` (`Perennial/TrustedCode/internal/bytealg.lean`). -/
theorem internal.bytealg.CountString.wp_proof :
    internal.bytealg.CountString.spec (GF := GF) (hG := hG) := fun s c => by
  wp_start
  wp_apply internal.bytealg.CountString.wp_loop s c (W64 0) (W64 0) ⟨by decide, by word, by simp [sint.nat]⟩
  iapply HΦ; itrivial

end proof

end Perennial
