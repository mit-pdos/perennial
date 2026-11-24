/-
The proof of `strings.Split`.
-/
module

public import Perennial.Spec.strings.Split
public import Perennial.Spec.strings.HasPrefix
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
variable [package_sem : strings.Assumptions]

/-- Proved from the Go model of `Split` (`goose/model/overlay/strings/strings.go`), which is stuck
for an empty `sep` (Go splits `s` into UTF-8 sequences there); the spec requires `sep ≠ []`. -/
theorem strings.Split.wp_proof
    (wp_HasPrefix : strings.HasPrefix.spec (GF := GF) (hG := hG)) :
    strings.Split.spec (GF := GF) (hG := hG) := by
  intro s sep Hsep
  wp_start as #Hinit
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hseplen
  have Hne : W64 (sep.length : Int) ≠ W64 0 := by
    have : 0 < sep.length := List.length_pos_iff.mpr Hsep
    word
  rw [decide_eq_false Hne]
  wp_auto
  ihave IH : iprop(∃ (a_sl : GoSlice) (fs : List GoString) (field rest : GoString),
      "a" ∷ a_ptr ↦ a_sl ∗
      "Ha" ∷ a_sl ↦* fs ∗
      "Hcap" ∷ ownSliceCap GoString a_sl (DFrac.own 1) ∗
      "field" ∷ field_ptr ↦ field ∗
      "rest" ∷ rest_ptr ↦ rest ∗
      "%Hinv" ∷ ⌜split s sep = fs ++ splitAux sep rest field⌝) $$ [a field rest]
  · iexists _, [], _, _
    iframe
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    ipureintro
    rfl
  wp_for IH
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hrlen
  wp_if_destruct
  · have Hif' := of_decide_eq_true (go.intoVal_inj Hif)
    obtain ⟨c, r, rfl⟩ : ∃ c r, rest = c :: r := by
      cases rest with
      | nil => exfalso; simp at Hif'
      | cons c r => exact ⟨c, r, rfl⟩
    wp_apply wp_HasPrefix
    by_cases hp : sep <+: c :: r
    · -- an occurrence of `sep`: the field ends
      simp only [hp, decide_true]
      wp_auto
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := GoString) (t := go.string) [field]
      wp_auto
      rw [show go.arrayLiteralSize
        [KeyedElement none (ElementExpression go.string #field)] = 1 from rfl]
      isplitl []
      · ipureintro; rfl
      iintro %sl_ptr ⟨Htmp, -⟩
      wp_auto
      wp_apply wp_slice_append (V := GoString) (t := go.string) a_sl fs _ [field] (DFrac.own 1)
        $$ [Ha Hcap Htmp] as %a' ⟨Ha', Hcap', -⟩
      · iframe
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
      have Hp : sep.length ≤ (c :: r).length := hp.length_le
      rw [ite_eq_left (by word)]
      rw [show sint.nat (W64 ((c :: r).length : Int)) = (c :: r).length by word,
        show sint.nat (W64 (sep.length : Int)) = sep.length by word,
        List.take_of_length_le (by simp)]
      wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro
      rw [Hinv, splitAux, ite_eq_left ⟨Hsep, hp⟩]
      simp
    · -- another byte: it goes to the field
      simp only [hp, decide_false]
      wp_auto
      rw [ite_eq_left (by simp only [List.length_cons] at Hrlen ⊢; word)]
      wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
      rw [ite_eq_left (by simp only [List.length_cons] at Hrlen ⊢; word)]
      rw [show sint.nat (W64 ((c :: r).length : Int)) = (c :: r).length by word,
        List.take_of_length_le (l := List.drop 1 (c :: r)) (by simp)]
      wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro
      rw [Hinv, splitAux, ite_eq_right (fun h => hp h.2)]
      simp
  · -- the end of `s`: the last field
    have Hnot : ¬ sint.Z (W64 0) < sint.Z (W64 rest.length) :=
      fun h => Hif (by rw [decide_eq_true h])
    simp only [decide_eq_false Hnot, Bool.false_eq_true, ↓reduceIte]
    have Hrest : rest = [] := List.eq_nil_of_length_eq_zero (by word)
    subst Hrest
    wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := GoString) (t := go.string) [field]
    wp_auto
    rw [show go.arrayLiteralSize
      [KeyedElement none (ElementExpression go.string #field)] = 1 from rfl]
    isplitl []
    · ipureintro; rfl
    iintro %sl_ptr ⟨Htmp, -⟩
    wp_apply wp_slice_append (V := GoString) (t := go.string) a_sl fs _ [field] (DFrac.own 1)
      $$ [Ha Hcap Htmp] as %a' ⟨Ha', Hcap', -⟩
    · iframe
    rw [Hinv, splitAux]
    iapply HΦ
    iframe

end proof

end Perennial
