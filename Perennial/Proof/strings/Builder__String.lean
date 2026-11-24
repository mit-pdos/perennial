/-
The proof of `strings.Builder.String` (its Go model, `goose/model/overlay/strings/builder.go`).
-/
module

public import Perennial.Spec.strings.Builder__String
public import Perennial.Spec.internal.gomodel.StartRead

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

/-- A byte's typed points-to is its heap points-to (`typedPointsto_w8`). -/
theorem strings.w8_typedPointsto_heap (l : Loc) (b : w8) (dq : DFrac) :
    typedPointsto (GF := GF) l b dq ⊢ heapPointsto l dq #b := by
  rw [typedPointsto_unseal_eq]
  change iprop(heapPointsto l dq #b ∗ ⌜l ≠ null⌝) ⊢ _
  iintro ⟨H, -⟩
  iexact H

theorem strings.Builder.String.wp_proof
    (wp_StartRead : internal.gomodel.StartRead.spec (GF := GF) (hG := hG)) :
    strings.Builder.String.spec (GF := GF) (hG := hG) := by
  intro l s
  wp_start as Hown
  unfold strings.ownBuilder
  icases Hown with ⟨%used, %buf, %dq, %Hnn, Haddr, Hbf, Hbuf, Hcap, %Hdq⟩
  imod ownSlice_persist $$ Hbuf with #Hbuf
  wp_auto
  wp_apply wp_bytes_to_string buf s DFrac.discard $$ Hbuf as -
  ihave %Hlen := ownSlice_len $$ Hbuf
  -- `forRange`'s counter is `i`; the model's own `i` (the key) is shadowed
  rename_i k_ptr
  irename : (k_ptr ↦ Perennial.zero_val w64 : IProp GF) => k
  -- the loop leaves a reader on each byte of `buf`, which needs only `Hbuf`
  ihave IH : iprop(∃ (n kv : w64),
      "i" ∷ i_ptr ↦ n ∗
      "k" ∷ k_ptr ↦ kv ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (s.length : Int)⌝) $$ [i k]
  · iexists _, _
    iframe
    ipureintro
    exact ⟨by word, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z n).toNat < s.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, s[(sint.Z n).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z buf.len from ⟨Hn.1, Hif⟩]
    wp_apply wp_load_slice_index buf (sint.Z n) s DFrac.discard x Hn.1 $$ [Hbuf]
    · isplit
      · iexact Hbuf
      · ipureintro; exact Hx
    iintro -
    wp_auto
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z buf.len from ⟨Hn.1, Hif⟩]
    icases ownSlice_elem_acc (sint.Z n) x buf DFrac.discard s Hn.1 Hx $$ Hbuf with ⟨He, -⟩
    ihave He := strings.w8_typedPointsto_heap _ _ _ $$ He
    wp_apply wp_StartRead $$ He
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro
    exact ⟨by word, by word⟩
  · iapply HΦ
    iexists used, buf, DFrac.discard
    iframe Haddr Hbf Hbuf Hcap
    ipureintro; exact ⟨Hnn, DFrac.valid_discard⟩

end proof

end Perennial
