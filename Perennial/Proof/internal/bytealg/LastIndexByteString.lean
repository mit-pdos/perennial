/-
The proof of `internal.bytealg.LastIndexByteString`.
-/
module

public import Perennial.Spec.internal.bytealg.LastIndexByteString
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
variable [package_sem : internal.bytealg.Assumptions]

theorem internal.bytealg.LastIndexByteString.wp_proof :
    internal.bytealg.LastIndexByteString.spec (GF := GF) (hG := hG) := by
  intro s c
  wp_start
  try wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl
  try wp_auto
  ihave HI : (∃ (j : Nat), "i" ∷ i_ptr ↦ W64 ((j : Int) - 1) ∗
      "%Hj" ∷ ⌜j ≤ s.length ∧
        internal.bytealg.lastIndexByte s c = internal.bytealg.lastIdxFrom s c j⌝ : IProp GF) $$ [i]
  · iexists s.length
    isplitl
    · rw [show W64 ((s.length : Int) - 1) = W64 (s.length : Int) - W64 1 by word]
      iexact i
    ipureintro; exact ⟨Nat.le_refl _, rfl⟩
  wp_for HI
  wp_if_destruct
  · -- `i >= 0`: `i = j - 1` with `j ≥ 1`
    rcases j with _ | k
    · exfalso; revert Hif; word
    have Hk : sint.nat (W64 (((k + 1 : Nat) : Int) - 1)) = k := by word
    have Hk0 : 0 ≤ sint.Z (W64 (((k + 1 : Nat) : Int) - 1)) := by word
    have Hlt : k < s.length := by omega
    obtain ⟨b, Hb⟩ : ∃ b, s[k]? = some b := ⟨_, List.getElem?_eq_getElem Hlt⟩
    try wp_auto
    simp only [Hk, Hk0, ↓reduceIte, Hb]
    try wp_auto
    have Hgd : s.getD k 0 = b := by simp [List.getD, Hb]
    wp_if_destruct
    · -- found
      try wp_auto
      wp_for_post
      have : internal.bytealg.lastIndexByte s c = k := by
        rw [Hj.2, internal.bytealg.lastIdxFrom, Hgd]; simp [Hif]
      rw [show W64 (((k + 1 : Nat) : Int) - 1) = W64 (internal.bytealg.lastIndexByte s c) by
        rw [this]; congr 1; omega]
      iapply HΦ
      ipureintro
      exact Hl
    · try wp_auto
      wp_for_post
      iframe
      iexists k
      isplitl
      · rw [show W64 ((k : Int) - 1) = W64 (((k + 1 : Nat) : Int) - 1) - W64 1 by word]
        iexact i
      ipureintro
      refine ⟨by omega, ?_⟩
      rw [Hj.2, internal.bytealg.lastIdxFrom, Hgd]; simp [Hif]
  · -- `i < 0`: `j = 0`
    rcases j with _ | k
    · rw [show W64 (-1) = W64 (internal.bytealg.lastIndexByte s c) by rw [Hj.2]; rfl]
      iapply HΦ
      ipureintro
      exact Hl
    · exfalso; apply Hif
      have := Hj.1
      word

end proof

end Perennial
