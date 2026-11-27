/-
The proof of `strings.IndexAny`.
-/
module

public import Perennial.Spec.strings.IndexAny
public import Perennial.Spec.strings.IndexRune
public import Perennial.Spec.strings.makeASCIISet
public import Perennial.Spec.strings.asciiSet__contains

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

theorem strings.IndexAny.wp_proof
    (wp_IndexRune : strings.IndexRune.spec (GF := GF) (hG := hG))
    (wp_makeASCIISet : strings.makeASCIISet.spec (GF := GF) (hG := hG))
    (wp_asciiSet__contains : strings.asciiSet.contains.spec (GF := GF) (hG := hG)) :
    strings.IndexAny.spec (GF := GF) (hG := hG) := by
  intro s chars
  wp_start as #Hinit
  wp_auto
  wp_if_destruct
  · iapply HΦ
    ipureintro
    intro _
    rw [strings.indexAnyByte_eq_neg s [] (fun _ _ _ h => nomatch h)]
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hcl
  wp_if_destruct
  · obtain ⟨b, rfl⟩ : ∃ b, chars = [b] := by
      have : chars.length = 1 := by revert Hif; word
      match chars, this with
      | [b], _ => exact ⟨b, rfl⟩
    simp only [List.getElem?_cons_zero]
    wp_auto
    wp_if_destruct
    · wp_apply wp_IndexRune
      iapply HΦ
      ipureintro
      intro hascii
      have := hascii b (List.mem_singleton_self b)
      exfalso; revert Hif; word
    · wp_apply wp_IndexRune
      iapply HΦ
      ipureintro
      intro hascii
      have h128 := hascii b (List.mem_singleton_self b)
      rw [strings.indexAnyByte_single]
      unfold strings.indexRune
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩),
        show W8 (sint.Z (W32 (uint.Z b))) = b by word]
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hsl
  wp_if_destruct
  wp_apply wp_makeASCIISet as %aset %ok ⟨%Hok, %Hlen, %Hhas⟩
  wp_if_destruct
  rotate_left
  · have hascii := Hok.1 rfl
    have Hhas := Hhas rfl
    irename «as» => Has
    ihave HI : (∃ (j : Nat), "i" ∷ i_ptr ↦ W64 (j : Int) ∗
        "%Hj" ∷ ⌜j ≤ s.length ∧ ∀ k < j, ∀ b, s[k]? = some b → b ∉ chars⌝ : IProp GF) $$ [i]
    · iexists 0
      iframe i
      ipureintro
      exact ⟨Nat.zero_le _, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
    wp_for HI
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    wp_if_destruct
    · simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif
      have Hjl : j < s.length := by have := Hj.1; revert Hif; word
      have Hk : sint.nat (W64 (j : Int)) = j := by word
      have Hk0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
      obtain ⟨b, Hb⟩ : ∃ b, s[j]? = some b := ⟨_, List.getElem?_eq_getElem Hjl⟩
      try wp_auto
      simp only [Hk, Hk0, ↓reduceIte, Hb]
      try wp_auto
      wp_apply wp_asciiSet__contains $$ Has as Has
      rw [Hhas b]
      by_cases hbc : b ∈ chars
      · simp only [hbc, decide_true]
        try wp_auto
        wp_for_post
        iapply HΦ
        ipureintro
        intro _
        rw [strings.indexAnyByte_eq_of s chars j b Hb hbc Hj.2]
      · simp only [hbc, decide_false]
        try wp_auto
        wp_for_post
        iframe
        iexists j + 1
        isplitl [i]
        · rw [show W64 (((j + 1 : Nat) : Int)) = W64 (j : Int) + W64 1 by word]
          iexact i
        ipureintro
        refine ⟨by omega, fun k hk b' hb' => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact Hj.2 k hk b' hb'
        · rw [Hb] at hb'; cases hb'; exact hbc
    · simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif
      have Hjl : j = s.length := by have := Hj.1; revert Hif; word
      simp only [Hif, decide_false]
      try wp_auto
      simp only [Bool.false_eq_true, ↓reduceIte]
      try wp_auto
      iapply HΦ
      ipureintro
      intro _
      rw [strings.indexAnyByte_eq_neg s chars (fun k b' hb' => Hj.2 k (by
        have := (List.getElem?_eq_some_iff.1 hb').1; omega) b' hb')]
  all_goals
    wp_apply (wp_string_for_range s _ (fun j => iprop(
        «$res0_ptr» ↦ zero_val w64 ∗ chars_ptr ↦ chars ∗ (∃ v : w32, c_ptr ↦ v) ∗
        (∃ k : w64, i_ptr ↦ k) ∗
        (∀ i : w64, ⌜(∀ b ∈ chars, uint.Z b < 128) → i = W64 (strings.indexAnyByte s chars)⌝ -∗
          Φ #i) ∗
        ⌜(∀ b ∈ chars, uint.Z b < 128) → ∀ j' < j, ∀ e, (go.runes s)[j']? = some e →
          strings.indexRune chars e.2 < 0⌝))) $$ [«$res0» chars c i HΦ]
    · iframe
      ipureintro
      intro _ j' hj'
      omega
    · imodintro
      iintro %j %k %rv %hk ⟨Hres, Hch, ⟨%v, Hc⟩, ⟨%k0, Hi⟩, HΦ, %HP⟩
      wp_auto
      wp_apply wp_IndexRune
      have hbd := strings.indexRune_bounds chars rv
      wp_if_destruct
      · have hnn : 0 ≤ strings.indexRune chars rv := by revert Hif; word
        iapply forRangePostcondition_return
        wp_auto
        iapply HΦ
        ipureintro
        intro hascii
        obtain ⟨h0, h1, hin⟩ := (strings.indexRune_ascii_chars chars hascii rv).1 hnn
        obtain ⟨b, hb, hb128, hrv⟩ :=
          go.runes_lt_0x80 s (k, rv) (List.mem_of_getElem? hk) ⟨h0, h1⟩
        have hbeq : W8 (sint.Z rv) = b := by simp only at hrv; rw [hrv]; word
        rw [hbeq] at hin
        rw [strings.indexAnyByte_eq_of s chars k b hb hin
          (strings.no_byte_of_chars s chars hascii j k (HP hascii)
            (fun j' e hj' hlt => strings.runes_idx_lt s j j' (k, rv) e hk hj' hlt))]
      · have hneg : strings.indexRune chars rv < 0 := by revert Hif; word
        iapply forRangePostcondition_do
        iframe
        ipureintro
        intro hascii j' hj' e he
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | rfl
        · exact HP hascii j' hj' e he
        · rw [hk] at he; cases he; exact hneg
    · iintro ⟨Hres, Hch, Hc, Hi, HΦ, %HP⟩
      wp_auto
      iapply HΦ
      ipureintro
      intro hascii
      rw [strings.indexAnyByte_eq_neg s chars (fun p b' hb' =>
        strings.no_byte_of_chars s chars hascii (go.runes s).length (s.length + 1) (HP hascii)
          (fun j' e hj' _ => (List.getElem?_eq_some_iff.1 hj').1) p
          (by have := (List.getElem?_eq_some_iff.1 hb').1; omega) b' hb')]

end proof

end Perennial
