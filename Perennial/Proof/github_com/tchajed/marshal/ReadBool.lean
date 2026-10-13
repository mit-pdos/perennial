/-
The proof of `github.com/tchajed/marshal.ReadBool`.
-/
module

public import Perennial.Spec.github_com.tchajed.marshal.ReadBool

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

theorem github_com.tchajed.marshal.ReadBool.wp_proof :
    github_com.tchajed.marshal.ReadBool.spec (GF := GF) (hG := hG) := fun s q bit tail => by
  wp_start as Hs
  ihave %Hsz := ownSlice_len _ _ _ $$ Hs
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
  simp only [List.length_cons] at Hsz
  have h1 : sint.Z (W64 1) = 1 := by decide
  have hs1 : 1 ≤ sint.Z s.len := by simp only [sint.nat, sint.Z] at *; omega
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by
    rw [show sint.Z (W64 0) = 0 from rfl]; omega⟩)]
  wp_apply wp_load_slice_index s _ _ q bit (by decide) $$ [Hs] with Hs
  · iframe Hs; ipureintro; rfl
  try wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [h1]; exact hs1, Hwf.2⟩)]
  wp_auto
  iapply HΦ
  rw [show bit :: tail = [bit] ++ tail from rfl]
  icases ownSlice_split_app (W64 1) s q [bit] tail rfl (by decide)
    (by simp only [List.cons_append, List.nil_append, List.length_cons]; exact Hsz.1) Hwf.1 $$ Hs
    with ⟨_, Hs⟩
  iframe Hs
  ipureintro
  by_cases hb : bit = W8 0
  · subst hb; decide
  · have : uint.Z bit ≠ 0 := fun h => hb (by simp only [uint.Z] at h; exact BitVec.eq_of_toNat_eq (by simp; omega))
    simp only [hb, this, decide_false, Bool.not_false, ne_eq, not_false_eq_true, decide_true]

end proof

end Perennial
