/-
The proof of `strings.Join`.
-/
module

public import Perennial.Spec.strings.Join
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

/-- Proved from the model of `Join` (`Perennial/TrustedCode/strings.lean`), which does not
model Go's panic when the result's length overflows `int`. -/
theorem strings.Join.wp_proof :
    strings.Join.spec (GF := GF) (hG := hG) := by
  intro elems xs dq sep
  wp_start as Hs
  wp_auto
  -- `forRange`'s counter is `i`; the model's own `i` (the key) is shadowed
  rename_i k_ptr
  irename : (k_ptr ↦ zero_val w64 : IProp GF) => k
  ihave %Hlen := ownSlice_len $$ Hs
  ihave IH : iprop(∃ (n kv : w64) (acc ev : GoString),
      "i" ∷ i_ptr ↦ n ∗
      "k" ∷ k_ptr ↦ kv ∗
      "s" ∷ s_ptr ↦ acc ∗
      "e" ∷ e_ptr ↦ ev ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (xs.length : Int)⌝ ∗
      "%Hacc" ∷ ⌜acc = sep.intercalate (xs.take (sint.Z n).toNat)⌝) $$ [i k s e]
  · iexists _, _, _, _
    iframe
    ipureintro
    exact ⟨⟨by word, by word⟩, by simp; rfl⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z n).toNat < xs.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, xs[(sint.Z n).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z elems.len from ⟨Hn.1, Hif⟩]
    wp_apply wp_load_slice_index elems (sint.Z n) xs dq x Hn.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hx
    wp_if_destruct
    all_goals
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ?_⟩
      have Hx' : xs[(sint.Z n).toNat] = x := by
        rw [List.getElem?_eq_getElem Hlt] at Hx; exact Option.some.inj Hx
      have Hsucc : (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 := by word
      rw [Hsucc, intercalate_take_succ sep xs _ x Hlt Hx']
    · simp [Hacc, show (sint.Z n).toNat ≠ 0 by word]
    · simp [Hacc, show (sint.Z n).toNat = 0 by word]
  · rw [Hacc, List.take_of_length_le (by word)]
    iapply HΦ
    iframe

end proof

end Perennial
