/-
The proof of `unicode/utf8.decodeRuneInStringSlow`.
-/
module

public import Perennial.Spec.unicode.utf8.decodeRuneInStringSlow
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
variable [package_sem : unicode.utf8.Assumptions]

set_option maxRecDepth 100000 in
theorem unicode.utf8.decodeRuneInStringSlow.wp_proof :
    unicode.utf8.decodeRuneInStringSlow.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start as #Hpkg
  ihave #Hinit := unicode.utf8.isInit_access $$ Hpkg
  icases Hinit with ⟨#Hfirst, #Hacc⟩
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hlen
  wp_if_destruct
  · iapply HΦ
    ipureintro
    left
    refine ⟨?_, rfl⟩
    apply List.eq_nil_of_length_eq_zero
    word
  obtain ⟨c, rest, rfl⟩ : ∃ c rest, s = c :: rest := by
    cases s with
    | nil => exact absurd (by decide) Hif
    | cons c rest => exact ⟨c, rest, rfl⟩
  wp_auto
  have hci : sint.Z (W64 (uint.Z c)) = uint.Z c := by word
  have hlen256 : unicode.utf8.firstVal.arr.length = 256 := rfl
  have hcl : (sint.Z (W64 (uint.Z c))).toNat < unicode.utf8.firstVal.arr.length := by
    rw [hlen256]; word
  rw [ite_eq_left (by word)]
  icases array_acc (V := w8) (globalAddr unicode.utf8.first) (sint.Z (W64 (uint.Z c))) _ _ _
    (unicode.utf8.firstVal.arr[(sint.Z (W64 (uint.Z c))).toNat]) (by word)
    (List.getElem?_eq_getElem hcl) $$ Hfirst with ⟨Hx, -⟩
  have hok := List.all_eq_true.mp unicode.utf8.firstVal_ok _ (List.getElem_mem hcl)
  generalize unicode.utf8.firstVal.arr[(sint.Z (W64 (uint.Z c))).toNat] = x at hok ⊢
  wp_auto
  wp_if_destruct
  · iapply HΦ
    ipureintro
    right
    refine ⟨List.cons_ne_nil _ _, by word, by simp; word⟩
  have hx : 2 ≤ BitVec.toNat (x &&& W8 7) ∧ BitVec.toNat (x &&& W8 7) ≤ 4 := by
    simp only [decide_eq_true_eq] at hok
    rcases hok with h | h
    · exfalso; apply Hif; word
    · exact h
  have hai : (sint.Z (W64 (uint.Z (x >>> W64 4)))).toNat < unicode.utf8.acceptRangesVal.arr.length := by
    rw [show unicode.utf8.acceptRangesVal.arr.length = 16 from rfl]; word
  rw [ite_eq_left (by word)]
  icases array_acc (globalAddr unicode.utf8.acceptRanges) (sint.Z (W64 (uint.Z (x >>> W64 4)))) _ _ _
    (unicode.utf8.acceptRangesVal.arr[(sint.Z (W64 (uint.Z (x >>> W64 4)))).toNat]) (by word)
    (List.getElem?_eq_getElem hai) $$ Hacc with ⟨Ha, -⟩
  generalize unicode.utf8.acceptRangesVal.arr[(sint.Z (W64 (uint.Z (x >>> W64 4)))).toNat] = ar
  wp_auto
  wp_if_destruct
  · iapply HΦ
    ipureintro
    right
    refine ⟨List.cons_ne_nil _ _, by word, by simp; word⟩
  have hn : uint.Z (x &&& W8 7) ≤ (c :: rest).length := by
    have := Hif; simp only [List.length_cons] at this ⊢; word
  obtain ⟨c1, rest, rfl⟩ : ∃ c1 rest', rest = c1 :: rest' := by
    cases rest with
    | nil => exfalso; simp only [List.length_cons, List.length_nil] at hn; word
    | cons c1 rest' => exact ⟨c1, rest', rfl⟩
  wp_auto
  repeat' (first | wp_if_destruct | wp_auto)
  all_goals try (iapply HΦ; ipureintro; right
                 refine ⟨List.cons_ne_nil _ _, by word, by simp only [List.length_cons]; word⟩)
  obtain ⟨c2, rest, rfl⟩ : ∃ c2 rest', rest = c2 :: rest' := by
    cases rest with
    | nil => exfalso; simp only [List.length_cons, List.length_nil] at hn; word
    | cons c2 rest' => exact ⟨c2, rest', rfl⟩
  wp_auto
  repeat' (first | wp_if_destruct | wp_auto)
  all_goals try (iapply HΦ; ipureintro; right
                 refine ⟨List.cons_ne_nil _ _, by word, by simp only [List.length_cons]; word⟩)
  obtain ⟨c3, rest, rfl⟩ : ∃ c3 rest', rest = c3 :: rest' := by
    cases rest with
    | nil => exfalso; simp only [List.length_cons, List.length_nil] at hn; word
    | cons c3 rest' => exact ⟨c3, rest', rfl⟩
  wp_auto
  repeat' (first | wp_if_destruct | wp_auto)
  all_goals try (iapply HΦ; ipureintro; right
                 refine ⟨List.cons_ne_nil _ _, by word, by simp only [List.length_cons]; word⟩)
  all_goals done

end proof

end Perennial
