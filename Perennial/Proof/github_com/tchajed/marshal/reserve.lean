/-
The proof of `github.com/tchajed/marshal.reserve`.
-/
module

public import Perennial.Spec.github_com.tchajed.marshal.reserve
public import Perennial.Spec.github_com.goose_lang.std.SumAssumeNoOverflow
public import Perennial.Spec.github_com.tchajed.marshal.compute_new_cap

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
variable [package_sem : github_com.tchajed.marshal.Assumptions]

theorem github_com.tchajed.marshal.reserve.wp_proof
    (wp_SumAssumeNoOverflow : github_com.goose_lang.std.SumAssumeNoOverflow.spec (GF := GF) (hG := hG))
    (wp_compute_new_cap : github_com.tchajed.marshal.compute_new_cap.spec (GF := GF) (hG := hG)) :
    github_com.tchajed.marshal.reserve.spec (GF := GF) (hG := hG) := fun s extra vs Hbound => by
  wp_start as ⟨Hs, Hcap⟩
  ihave %Hsz := ownSlice_len _ _ _ $$ Hs
  ihave %Hcapwf := ownSliceCap_wf _ _ $$ Hcap
  ihave #Hstd : isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_SumAssumeNoOverflow s.len extra as %Hsum
  wp_if_destruct
  · wp_apply wp_compute_new_cap s.cap (s.len + extra) as %new_cap ⟨%Hnc, %Hnc'⟩
    have hlen : 0 ≤ sint.Z s.len ∧ sint.Z s.len ≤ sint.Z new_cap := by
      have := Hsz.1
      refine ⟨Hcapwf.1, ?_⟩
      rcases Hnc' with h | h <;> subst h <;> word
    wp_apply wp_slice_make3 (V := w8) s.len new_cap hlen as %sl ⟨Hsl, Hslcap, %Hslc⟩
    ihave %Hsllen := ownSlice_len _ _ _ $$ Hsl
    ihave %Hslwf := ownSliceCap_wf _ _ $$ Hslcap
    wp_apply wp_slice_copy (V := w8) (t := go.byte) sl _ s vs (DFrac.own 1) $$ [$Hsl $Hs]
      as %n ⟨%Hn, Hsl, Hs⟩
    iapply HΦ
    rw [List.length_replicate, ← Hsz.1, List.take_length,
      List.drop_eq_nil_of_le (by simp), List.append_nil]
    iframe Hsl Hslcap
    ipureintro
    simp only [List.length_replicate] at Hsllen
    subst Hslc
    have := Hsz.1
    word
  · iapply HΦ
    iframe Hs Hcap
    ipureintro
    word

end proof

end Perennial
