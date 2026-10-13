/-
The proof of `sync.NewCond`.
-/
module

public import Perennial.Spec.sync.NewCond

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem sync.NewCond.wp_proof :
    sync.NewCond.spec (GF := GF) (hG := hG) := by
  intro m
  wp_start as _
  wp_auto
  wp_pures
  wp_apply_core wp_alloc _
  iintro %c ⟨Hc, %Hal⟩
  have hck := go.field_aligned (V := Cond) (f := go!"checker") (by solve_layout_mem)
    (by solve_layout_nodup) (by solve_layout_pow2) Hal.1 Hal.2
  iStructNamed Hc
  ipersist L
  ipersist notify
  imod inv_alloc copyCheckerN ⊤ (copyCheckerInv _) $$ [checker] with #Hchecker
  · inext; ileft; iexact checker
  wp_pures
  iapply HΦ
  rw [isCond_unseal]; unfold isCondDef
  rw [isCopyChecker_unseal]; unfold isCopyCheckerDef
  simp only [named]
  iframe #
  ipureintro; simpa [Aligned, Encoding.align] using hck

end proof

end Perennial
