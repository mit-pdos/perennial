/-
The proof of `pageSize`: the header, the elements and each inode's key and value.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.pageSize

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE
open github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.pageSize.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.pageSize.spec (GF := GF) (hG := hG) := by
  intro s ms
  wp_start as #Hin
  unfold inodesOwn
  icases Hin with ⟨%xs, #Hs, #Hxs⟩
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hxs
  ihave %Hslen := ownSlice_len _ _ _ $$ Hs
  have hlenW : s.len = W64 (ms.length : Int) := w64_of_sint_nat _ _ (Hlen ▸ Hslen.1) Hslen.2
  wp_auto
  ihave HI : (∃ (j : w64) (it : inode),
      "i" ∷ i_ptr ↦ j ∗
      "item" ∷ item_ptr ↦ it ∗
      "sz" ∷ sz_ptr ↦ W64 ((16 + 16 * ms.length + (dataBytes (ms.take (sint.nat j))).length : Nat) : Int) ∗
      "HΦ" ∷ (True -∗ Φ #(W64 ((16 + (pageBody true ms).length : Nat) : Int))) ∗
      "«$res0»" ∷ «$res0_ptr» ↦ zero_val w64 ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ ms.length⌝ : IProp GF) $$ [i item sz HΦ «$res0»]
  · iexists (W64 0), _
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, show dataBytes [] = [] from rfl,
      List.length_nil, Nat.add_zero,
      show W64 (((16 + 16 * ms.length : Nat)) : Int) = W64 16 + s.len * W64 16 by
        rw [hlenW]; push_cast; word]
    iframe
    ipureintro; refine ⟨by decide, ?_⟩; simp
  wp_for HI
  have hsZ : sint.Z s.len = ms.length := sint_Z_eq_of_sint_nat _ _ (Hlen ▸ Hslen.1) Hslen.2
  wp_if_destruct
  · -- an iteration
    rw [hsZ] at Hif
    have hjZ : sint.Z j = (sint.nat j : Int) := by
      simp only [sint.nat]; rw [Int.toNat_of_nonneg Hj.1]
    have hjn : sint.nat j < ms.length := by omega
    obtain ⟨x, hx⟩ : ∃ x, xs[sint.nat j]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hm : ms[sint.nat j]? = some ms[sint.nat j] := List.getElem?_eq_getElem hjn
    have hdsucc := dataBytes_take_succ ms (sint.nat j) hjn
    generalize ms[sint.nat j] = m at hm hdsucc
    ihave Hx := BigSepL2.bigSepL2_lookup hx hm $$ Hxs
    unfold inodeOwn
    icases Hx with ⟨%Hxfp, #Hkey, #Hval⟩
    ihave %Hkl := ownSlice_len _ _ _ $$ Hkey
    ihave %Hvl := ownSlice_len _ _ _ $$ Hval
    simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len from ⟨Hj.1, by omega⟩, _root_.and_self,
      ite_true]
    wp_apply wp_load_slice_index s (sint.Z j) xs DFrac.discard x Hj.1 as -
    · isplitr
      · iexact Hs
      · ipureintro; rw [show (sint.Z j).toNat = sint.nat j from rfl]; exact hx
    have hkW : x.key'.len = W64 (m.key.length : Int) := w64_of_sint_nat _ _ Hkl.1 Hkl.2
    have hvW : x.value'.len = W64 (m.value.length : Int) := w64_of_sint_nat _ _ Hvl.1 Hvl.2
    wp_for_post
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
      show (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1
      have : sint.Z (j + W64 1) = sint.Z j + 1 := by word
      omega
    iexists (j + W64 1), x
    rw [hj1, hdsucc, List.length_append, show m.kv.length = m.key.length + m.value.length by
      simp [InodeM.kv]]
    iframe
    isplitl [sz]
    · iapply typedPointsto_of_eq
      iframe sz
      ipureintro
      push_cast; word
    ipureintro
    constructor <;> word
  · -- the end of the loop
    have hjn : sint.nat j = ms.length := by
      rw [hsZ] at Hif; have : sint.nat j = (sint.Z j).toNat := rfl; omega
    rw [hjn, List.take_of_length_le (Nat.le_refl _), show 16 + 16 * ms.length +
      (dataBytes ms).length = 16 + (pageBody true ms).length by rw [pageBody_length]; omega]
    iapply HΦ
    itrivial

end proof

end Perennial
