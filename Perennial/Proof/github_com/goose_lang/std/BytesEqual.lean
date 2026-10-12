/-
The proof of `github.com/goose-lang/std.BytesEqual`.
-/
module

public import Perennial.Spec.github_com.goose_lang.std.BytesEqual

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.goose_lang.std.Assumptions]

theorem github_com.goose_lang.std.BytesEqual.wp_proof :
    github_com.goose_lang.std.BytesEqual.spec (GF := GF) (hG := hG) :=
    fun s1 s2 xs1 xs2 dq1 dq2 => by
  wp_start as ⟨Hs1, Hs2⟩
  wp_auto
  ihave %Hl1 := ownSlice_len _ _ _ $$ Hs1
  ihave %Hl2 := ownSlice_len _ _ _ $$ Hs2
  by_cases hlen : s1.len = s2.len
  · simp only [hlen, _root_.decide_true, Bool.not_true]
    wp_auto
    have hl : xs1.length = xs2.length := by rw [Hl1.1, Hl2.1, hlen]
    ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗
        "%Hbound" ∷ ⌜uint.Z i ≤ xs1.length⌝ ∗
        "%Hi" ∷ ⌜∀ n : Nat, n < uint.nat i → xs1[n]? = xs2[n]?⌝ : IProp GF) $$ [i]
    · iexists (W64 0); iframe; ipureintro
      exact ⟨by simp [uint.Z], fun n h => by simp [uint.nat] at h⟩
    wp_for HI
    by_cases Hif : uint.Z i < uint.Z s2.len
    · simp only [Hif, _root_.decide_true, ↓reduceIte]
      wp_auto
      have hi := sint_nonneg_of_lt i s2.len Hif Hl2.2
      have hi1 : sint.Z i < sint.Z s1.len := by rw [hlen]; simp only [sint.Z, uint.Z] at *; word
      have hi2 : sint.Z i < sint.Z s2.len := by simp only [sint.Z, uint.Z] at *; word
      list_elem xs1 (sint.nat i) as a
      list_elem xs2 (sint.nat i) as b
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hi.1, hi1⟩)]
      wp_apply wp_load_slice_index s1 (sint.Z i) xs1 dq1 a hi.1 $$ [Hs1] with Hs1
      · iframe Hs1; ipureintro; exact Ha_lookup
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hi.1, hi2⟩)]
      wp_apply wp_load_slice_index s2 (sint.Z i) xs2 dq2 b hi.1 $$ [Hs2] with Hs2
      · iframe Hs2; ipureintro; exact Hb_lookup
      by_cases hab : a = b
      · subst hab
        simp only [_root_.decide_true, Bool.not_true]
        wp_auto
        wp_for_post
        iframe
        iexists (i + W64 1)
        iframe
        ipureintro
        have hu : uint.Z (i + W64 1) = uint.Z i + 1 := by simp only [sint.Z, uint.Z] at *; word
        constructor
        · simp only [sint.nat, sint.Z, uint.Z] at *; omega
        · intro n hn
          by_cases hn' : n < uint.nat i
          · exact Hi n hn'
          · have : n = sint.nat i := by simp only [sint.nat, uint.nat, sint.Z, uint.Z] at *; omega
            subst this; rw [Ha_lookup, Hb_lookup]
      · simp only [hab, _root_.decide_false, Bool.not_false]
        wp_auto
        wp_for_post
        rw [decide_eq_false (fun h => hab (by subst h; rw [Ha_lookup] at Hb_lookup; exact Option.some.inj Hb_lookup))]
        wp_end
    · simp only [Hif, _root_.decide_false, Bool.false_eq_true, ↓reduceIte]
      wp_auto
      have hl2u := github_com.goose_lang.std.std_core.sint_eq_uint _ Hl2.2
      rw [decide_eq_true (List.ext_getElem? fun n => by
        by_cases hn : n < uint.nat i
        · exact Hi n hn
        · rw [List.getElem?_eq_none (by simp only [sint.nat, uint.nat, sint.Z, uint.Z] at *; omega),
            List.getElem?_eq_none (by simp only [sint.nat, uint.nat, sint.Z, uint.Z] at *; omega)])]
      wp_end
  · simp only [hlen, _root_.decide_false, Bool.not_false]
    wp_auto
    rw [decide_eq_false (fun h => hlen (by
      have := congrArg List.length h
      simp only [sint.nat, sint.Z] at *
      apply BitVec.eq_of_toInt_eq; omega))]
    wp_end

end proof

end Perennial
