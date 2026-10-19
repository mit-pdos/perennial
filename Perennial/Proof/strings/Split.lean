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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

/-- Proved from the model of `Split` (`Perennial/TrustedCode/strings.lean`), which does not
model Go's split of `s` into UTF-8 sequences for an empty `sep`. -/
theorem strings.Split.wp_proof
    (wp_HasPrefix : strings.HasPrefix.spec (GF := GF) (hG := hG)) :
    strings.Split.spec (GF := GF) (hG := hG) := by
  intro s sep Hsep
  wp_start as #Hinit
  obtain ⟨c0, Hc0⟩ : ∃ c0, sep[0]? = some c0 := by
    cases sep with
    | nil => exact absurd rfl Hsep
    | cons c _ => exact ⟨c, rfl⟩
  wp_auto
  rw [Hc0]
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
    -- the model calls `HasPrefix` by its name (the trusted code is below `Code.strings`)
    rw [show (go!"strings.HasPrefix" : GoString) = HasPrefix from rfl]
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
      wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
      ihave %Hlen := ownSlice_len $$ Hsl
      ihave %Hwf := ownSlice_wf $$ Hsl
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
      have Hp : sep.length ≤ (c :: r).length := hp.length_le
      have Hk : 0 ≤ sint.Z (W64 sep.length) ∧ sint.Z (W64 sep.length) ≤ sint.Z sl.len := by word
      rw [ite_eq_left ⟨Hk.1, Hk.2, Hwf.2⟩]
      icases (ownSlice_split_all (W64 sep.length) sl _ _ Hk).1 $$ Hsl with ⟨-, Hsl⟩
      rw [show sint.nat (W64 sep.length) = sep.length by word]
      wp_apply wp_bytes_to_string $$ Hsl as -
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
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := w8) (t := go.byte) [c]
      wp_auto
      rw [show go.arrayLiteralSize
        [KeyedElement none (ElementExpression go.byte #c)] = 1 from rfl]
      isplitl []
      · ipureintro; rfl
      iintro %c_sl ⟨Hc_sl, -⟩
      wp_apply wp_bytes_to_string $$ Hc_sl as -
      wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
      ihave %Hlen := ownSlice_len $$ Hsl
      ihave %Hwf := ownSlice_wf $$ Hsl
      have Hk : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z sl.len := by
        simp only [List.length_cons] at Hlen Hrlen; word
      rw [ite_eq_left ⟨Hk.1, Hk.2, Hwf.2⟩]
      icases (ownSlice_split_all (W64 1) sl _ _ Hk).1 $$ Hsl with ⟨-, Hsl⟩
      rw [show sint.nat (W64 1) = 1 by word]
      wp_apply wp_bytes_to_string $$ Hsl as -
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
