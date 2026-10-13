/-
The proof of `github.com/goose-lang/primitive/disk.Read`.
-/
module

public import Perennial.Spec.github_com.goose_lang.primitive.disk.Read

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

/-- Proved directly from the disk FFI lifting lemma `wp_ReadOp`, rather than derived from
the atomic spec `wp_Read_atomic`. -/
theorem github_com.goose_lang.primitive.disk.Read.wp_proof :
    github_com.goose_lang.primitive.disk.Read.spec (GF := GF) (hG := hG) := by
  intro a q b
  wp_start as Hda
  wp_bind (ExternalOp _ _)
  wp_apply_core wp_ReadOp a q b $$ [Hda]
  · iexact Hda
  iintro %l ⟨Hda, Hl⟩
  ihave %Hnn := pointstoBlock_non_null l _ b $$ Hl
  wp_auto
  simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
    show (W64 4096 - W64 0 : w64) = W64 4096 from rfl, if_neg Hnn]
  wp_pures
  iapply HΦ
  iframe Hda
  unfold isBlockFull
  iapply block_array_to_slice (slice.mk l (W64 4096) (W64 4096)) (DFrac.own 1) b
    (by rw [Vector.length_toList]; rfl) ⟨(by decide : (0 : Int) ≤ sint.Z (W64 4096)), Int.le_refl _⟩ $$ Hl

end proof

end Perennial
