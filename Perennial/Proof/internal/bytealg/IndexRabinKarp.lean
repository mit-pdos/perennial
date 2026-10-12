/-
The proof of `internal.bytealg.IndexRabinKarp`.
-/
module

public import Perennial.Spec.internal.bytealg.IndexRabinKarp
public import Perennial.Spec.internal.bytealg.HashStr
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

theorem internal.bytealg.IndexRabinKarp.wp_proof
    (wp_HashStr : internal.bytealg.HashStr.spec (GF := GF) (hG := hG)) :
    internal.bytealg.IndexRabinKarp.spec (GF := GF) (hG := hG) := fun s sep Hlen => by
  wp_start
  wp_auto
  wp_apply wp_HashStr
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hsep
  -- the hash of the first `len(sep)` bytes
  ihave IH : iprop(∃ i : w64,
      "i" ∷ i_ptr ↦ i ∗
      "h" ∷ h_ptr ↦ rkHash (s.take (sint.nat i)) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sep.length⌝) $$ [i h]
  · iexists (W64 0)
    rw [show rkHash (s.take (sint.nat (W64 0))) = W32 0 from rfl]
    iframe
    ipureintro
    exact ⟨by decide, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hif' := Hif
    have hlt : sint.nat i < s.length := by word
    obtain ⟨c, hc⟩ : ∃ c, s[sint.nat i]? = some c := ⟨_, List.getElem?_eq_getElem hlt⟩
    simp only [Hi.1, ↓reduceIte, hc]
    wp_auto
    wp_for_post
    iframe
    iexists (i + W64 1)
    have Htake : s.take (sint.nat (i + W64 1)) = s.take (sint.nat i) ++ [c] := by
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, List.take_add_one, hc]; rfl
    rw [Htake, rkHash_snoc, show (W32 16777619 : w32) = primeRK from rfl]
    iframe
    ipureintro
    exact ⟨by word, by word⟩
  have Hnot := Hif
  have Hin : sint.nat i = sep.length := by word
  rw [Hin]
  -- an occurrence at 0
  have Hocc0 := slice_eq_iff_occ s sep 0
  rw [List.drop_zero] at Hocc0
  have Hlen0 : sint.nat (W64 (sep.length : Int)) - 0 = sep.length := by word
  wp_join (Q := fun v => iprop(
      (⌜v = executeVal ∧ ¬ sep <+: s⌝ ∨ ⌜v = returnVal #(W64 0) ∧ sep <+: s⌝) ∗
      sep_ptr ↦ sep ∗ s_ptr ↦ s ∗ n_ptr ↦ W64 sep.length ∗
      hashss_ptr ↦ rkHash sep ∗ h_ptr ↦ rkHash (s.take sep.length)))
    with [sep s n hashss h]
  · rw [ite_eq_left ⟨by decide, by word, by word⟩]
    wp_auto
    simp only [Hlen0, List.drop_zero]
    wp_if_destruct
    · iframe
      iright
      ipureintro
      exact ⟨trivial, Hocc0.1 Hif⟩
    · iframe
      ileft
      ipureintro
      exact ⟨trivial, fun h => Hif (Hocc0.2 h)⟩
  · iframe
    ileft
    ipureintro
    exact ⟨trivial, fun h => Hif (by rw [Hocc0.2 h])⟩
  iintro ⟨Hv, sep, s, n, hashss, h⟩
  icases Hv with (%Hv | %Hv)
  rotate_left
  · obtain ⟨rfl, Hocc⟩ := Hv
    wp_auto
    rw [indexResult_of_occ s sep (W64 0) (by decide) (by word)
      (by rw [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]; exact Hocc)
      (fun j hj => by simp at hj; omega)]
    iapply HΦ; itrivial
  obtain ⟨rfl, Hn0⟩ := Hv
  wp_auto
  -- the rolling hash of the window `s[i-n:i]`
  have Hsep0 : sep ≠ [] := by rintro rfl; exact Hn0 (List.nil_prefix)
  have HN : 0 < sep.length := List.length_pos_iff.2 Hsep0
  ihave IH2 : iprop(∃ i : w64,
      "i" ∷ i_ptr ↦ i ∗
      "h" ∷ h_ptr ↦ rkHash ((s.drop (sint.nat i - sep.length)).take sep.length) ∗
      "%Hi" ∷ ⌜sep.length ≤ sint.Z i ∧ sint.Z i ≤ s.length ∧
        ∀ j, j ≤ sint.nat i - sep.length → ¬ sep <+: s.drop j⌝) $$ [i h]
  · iexists _
    rw [show sint.nat (W64 (sep.length : Int)) - sep.length = 0 by word, List.drop_zero]
    iframe
    ipureintro
    refine ⟨by word, by word, fun j hj => ?_⟩
    obtain rfl : j = 0 := by omega
    exact Hn0
  wp_for IH2
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hs
  wp_if_destruct
  · have Hif' := of_decide_eq_true (go.intoVal_inj Hif)
    have hI : sint.nat i < s.length := by word
    have hIN : sep.length ≤ sint.nat i := by word
    obtain ⟨c0, c, w, Hw0, Hw1, Hc0, Hc, Hwlen⟩ :=
      window_step s (sint.nat i - sep.length) sep.length HN (by omega)
    rw [show sint.nat i - sep.length + sep.length = sint.nat i by omega] at Hc
    have Hia : sint.nat (i - W64 sep.length) = sint.nat i - sep.length := by word
    simp only [show 0 ≤ sint.Z i by word, ↓reduceIte, Hc]
    wp_auto
    simp only [show 0 ≤ sint.Z (i - W64 sep.length) by word, ↓reduceIte, Hia, Hc0]
    wp_auto
    have Hroll : rkHash ((s.drop (sint.nat i - sep.length)).take sep.length) * W32 16777619 +
          W32 (uint.Z c) - primeRK ^ sep.length * W32 (uint.Z c0) =
        rkHash ((s.drop (sint.nat i - sep.length + 1)).take sep.length) := by
      rw [Hw0, Hw1, show (W32 16777619 : w32) = primeRK from rfl, ← Hwlen]
      exact rkHash_roll c0 c w
    rw [Hroll]
    have Hi1 : sint.nat (i + W64 1) - sep.length = sint.nat i - sep.length + 1 := by word
    have Hi1' : sint.nat (i + W64 1 - W64 sep.length) = sint.nat i - sep.length + 1 := by word
    -- the invariant for `i + 1`, when the window at `i + 1 - n` is not `sep`
    have Hnext : ¬ (s.drop (sint.nat i - sep.length + 1)).take sep.length = sep →
        sep.length ≤ sint.Z (i + W64 1) ∧ sint.Z (i + W64 1) ≤ s.length ∧
        ∀ j, j ≤ sint.nat i - sep.length + 1 → ¬ sep <+: s.drop j := by
      intro Hne
      refine ⟨by word, by word, fun j hj => ?_⟩
      rcases Nat.lt_or_ge j (sint.nat i - sep.length + 1) with hj' | hj'
      · exact Hi.2.2 j (by omega)
      · obtain rfl : j = sint.nat i - sep.length + 1 := by omega
        rw [← slice_eq_iff_occ]; exact Hne
    wp_if_destruct
    · -- the hashes match: compare the bytes
      rw [ite_eq_left ⟨by word, by word, by word⟩]
      wp_auto
      rw [Hi1', show sint.nat (i + W64 1) - (sint.nat i - sep.length + 1) = sep.length by word]
      wp_if_destruct
      · -- an occurrence at `i + 1 - n`, the first
        wp_for_post
        rw [indexResult_of_occ s sep (i + W64 1 - W64 sep.length) (by word) (by word)
          (by rw [Hi1']; exact (slice_eq_iff_occ _ _ _).1 Hif)
          (fun j hj => Hi.2.2 j (by rw [Hi1'] at hj; omega))]
        iapply HΦ; itrivial
      · wp_for_post
        iframe
        iexists _
        rw [Hi1]
        iframe
        ipureintro
        exact Hnext Hif
    · wp_for_post
      iframe
      iexists _
      rw [Hi1]
      iframe
      ipureintro
      exact Hnext (fun h => Hif (by rw [h]))
  · have Hnot : ¬ sint.Z i < sint.Z (W64 s.length) := fun h => Hif (by rw [decide_eq_true h])
    simp only [decide_eq_false Hnot, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    rw [indexResult_of_none s sep ?_]
    · iapply HΦ; itrivial
    intro j hj
    rcases Nat.lt_or_ge j (sint.nat i - sep.length + 1) with hj' | hj'
    · exact Hi.2.2 j (by omega)
    · exact not_occ_of_short s sep Hsep0 j (by word)

end proof

end Perennial
