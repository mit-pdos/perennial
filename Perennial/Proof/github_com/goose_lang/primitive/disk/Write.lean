/-
The proof of `github.com/goose-lang/primitive/disk.Write`.
-/
module

public import Perennial.Spec.github_com.goose_lang.primitive.disk.Write

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode disk_ffi

section proof
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.goose_lang.primitive.disk.Assumptions]

/-- Proved directly from the disk FFI lifting lemma `wp_WriteOp`, rather than derived from
the atomic spec `wp_Write_atomic`. -/
theorem github_com.goose_lang.primitive.disk.Write.wp_proof :
    github_com.goose_lang.primitive.disk.Write.spec (GF := GF) (hG := hG) := by
  intro a s q b
  wp_start as ⟨%b0, Hda, Hs⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
  have hpos : sint.Z (W64 0) < sint.Z s.len := by
    rw [Vector.length_toList] at Hlen
    simp only [sint.nat, sint.Z, blockBytes] at *; simp; omega
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, hpos⟩)]
  simp only [sliceIndexRef, show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0]
  wp_pures
  wp_apply_core wp_WriteOp a b q s.ptr $$ [Hda Hs]
  · isplitl [Hda]
    · iexists b0; iexact Hda
    iapply slice_to_block_array $$ Hs
  iintro ⟨Hda, Hl⟩
  iapply HΦ
  iframe Hda
  iapply block_array_to_slice s q b (by simp only [sint.nat] at *; omega) Hwf $$ Hl

end proof

end Perennial
