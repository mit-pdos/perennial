/-
The proof of `strings.Count`.
-/
module

public import Perennial.Spec.strings.Count
public import Perennial.Spec.strings.Index
public import Perennial.Spec.internal.bytealg.CountString
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
variable [package_sem : strings.Assumptions]

theorem strings.Count.wp_proof
    (wp_Index : strings.Index'.spec (GF := GF) (hG := hG))
    (wp_CountString : internal.bytealg.CountString.spec (GF := GF) (hG := hG)) :
    strings.Count.spec (GF := GF) (hG := hG) := fun s sep Hsep Hs => by
  wp_start
  wp_auto
  have Hpos := List.length_pos_iff.2 Hsep
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hsepl
  rw [decide_eq_false (show ¬ W64 sep.length = W64 0 by word)]
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
  wp_if_destruct
  · -- one byte: `bytealg.CountString(s, sep[0])`
    obtain ⟨c, rfl⟩ : ∃ c, sep = [c] := List.length_eq_one_iff.1 (by word)
    simp only [show (0 : Int) ≤ sint.Z (W64 0) by decide, ↓reduceIte, List.getElem?_cons_zero]
    wp_auto
    wp_apply wp_CountString
    rw [countOcc_singleton]
    iapply HΦ; itrivial
  ihave IH : iprop(∃ (cur : GoString) (k : Nat),
      "s" ∷ s_ptr ↦ cur ∗
      "n" ∷ n_ptr ↦ W64 k ∗
      "%Hk" ∷ ⌜countOcc s sep = k + countOcc cur sep ∧ cur.length ≤ s.length⌝) $$ [s n]
  · iexists s, 0
    iframe
    ipureintro
    omega
  wp_for IH
  wp_apply wp_Index
  rcases internal.bytealg.indexResult_cases cur sep with ⟨j, hj, hres, hjle⟩ | ⟨hj, hres⟩
  · -- an occurrence at `j`: count it and go on after it
    have Hend := firstOcc_end_le cur sep j hj
    rw [hres, decide_eq_false (show ¬ W64 j = W64 (-1) by word)]
    wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hcur
    rw [ite_eq_left ⟨by word, by word, by word⟩,
      show sint.nat (W64 j + W64 sep.length) = j + sep.length by word,
      List.take_of_length_le (by simp; word)]
    wp_auto
    wp_for_post
    iframe
    iexists _, k + 1
    rw [show W64 k + W64 1 = W64 (k + 1 : Nat) by word]
    iframe
    ipureintro
    rw [countOcc_some cur sep Hsep j hj] at Hk
    exact ⟨by omega, by simp; omega⟩
  · -- no more occurrences: `n` is the count
    rw [hres]
    wp_auto
    wp_for_post
    rw [Hk.1, countOcc_none cur sep Hsep hj, Nat.add_zero]
    iapply HΦ; itrivial

end proof

end Perennial
