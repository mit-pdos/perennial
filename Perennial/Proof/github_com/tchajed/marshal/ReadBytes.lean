/-
The proof of `github.com/tchajed/marshal.ReadBytes`.
-/
module

public import Perennial.Spec.github_com.tchajed.marshal.ReadBytes

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.tchajed.marshal.Assumptions]

theorem github_com.tchajed.marshal.ReadBytes.wp_proof :
    github_com.tchajed.marshal.ReadBytes.spec (GF := GF) (hG := hG) := fun s dq len head tail Hlen => by
  wp_start as Hs
  ihave %Hsz := ownSlice_len _ _ _ $$ Hs
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
  simp only [List.length_append] at Hsz
  have hu : uint.Z len ≤ sint.Z s.len := by
    have := Hwf.1; simp only [sint.nat, uint.nat, sint.Z, uint.Z] at *; omega
  have he := sint_of_uint_le len _ hu (sint_lt_2_63 _)
  have hl : sint.Z len = uint.Z len ∧ 0 ≤ sint.Z len ∧ sint.Z len ≤ sint.Z s.len := by
    have := uint_Z_nonneg len
    refine ⟨he, ?_, ?_⟩ <;> omega
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, hl.2.1, by have := Hwf.2; omega⟩)]
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hl.2.1, hl.2.2, Hwf.2⟩)]
  wp_auto
  iapply HΦ
  icases ownSlice_split_app len s dq head tail
    (by simp only [sint.nat, uint.nat, sint.Z, uint.Z] at *; omega) hl.2.1
    (by simp only [List.length_append]; omega) Hwf.1 $$ Hs with ⟨H1, H2⟩
  iframe

end proof

end Perennial
