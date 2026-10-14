/-
The proof of `github.com/tchajed/marshal.ReadBytesCopy`.
-/
module

public import Perennial.Spec.github_com.tchajed.marshal.ReadBytesCopy

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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.tchajed.marshal.Assumptions]

theorem github_com.tchajed.marshal.ReadBytesCopy.wp_proof :
    github_com.tchajed.marshal.ReadBytesCopy.spec (GF := GF) (hG := hG) := fun s q len head tail Hlen => by
  wp_start as Hs
  ihave %Hsz := ownSlice_len _ _ _ $$ Hs
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
  simp only [List.length_append] at Hsz
  have hu : uint.Z len ≤ sint.Z s.len := by
    have := Hwf.1; simp only [sint.nat, uint.nat, sint.Z, uint.Z] at *; omega
  have he := sint_of_uint_le len _ hu (sint_lt_2_63 _)
  have hl : 0 ≤ sint.Z len ∧ sint.Z len ≤ sint.Z s.len := by
    have := uint_Z_nonneg len
    refine ⟨?_, ?_⟩ <;> omega
  wp_auto
  wp_apply wp_slice_make2 (V := w8) len $$ [] as %sl ⟨Hsl, Hcap⟩
  · ipureintro; exact hl.1
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, hl.1, by have := Hwf.2; omega⟩)]
  have hhd : sint.nat len = head.length := by simp only [sint.nat, uint.nat, sint.Z, uint.Z] at *; omega
  icases ownSlice_split_app len s q head tail hhd hl.1
    (by simp only [List.length_append]; omega) Hwf.1 $$ Hs with ⟨Hhead, Htail⟩
  wp_auto
  wp_apply wp_slice_copy (V := w8) (t := go.byte) sl _ _ head q $$ [$Hsl $Hhead]
    as %n ⟨%Hn, Hsl, Hhead⟩
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hl.1, hl.2, Hwf.2⟩)]
  wp_auto
  iapply HΦ
  iframe Htail
  rw [List.length_replicate, hhd, List.take_length, List.drop_eq_nil_of_le (by simp),
    List.append_nil]
  iexact Hsl

end proof

end Perennial
