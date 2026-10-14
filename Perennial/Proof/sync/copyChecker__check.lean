/-
The proof of `sync.(*copyChecker).check`.
-/
module

public import Perennial.Spec.sync.copyChecker__check

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem sync.copyChecker.check.wp_proof :
    sync.copyChecker.check.spec (GF := GF) (hG := hG) := by
  intro c
  wp_start as #Hinv
  rw [isCopyChecker_unseal]; unfold isCopyCheckerDef
  -- first `uintptr(*c) != uintptr(unsafe.Pointer(c))`
  wp_bind (Primitive1 _ _)
  iinv Hinv with >Hi
  icases Hi with (Hc | #Hc)
  · wp_apply_core wp_atomic_load _ _ c _ (null : Loc) $$ Hc
    iintro Hc
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hc
    imodintro
    isplitl [Hc]
    · inext; ileft; iexact Hc
    wp_auto
    rw [decide_eq_false (Ne.symm Hnn)]
    wp_auto
    -- `CompareAndSwapUintptr(c, 0, c)`
    wp_bind (CmpXchg _ _ _)
    iinv Hinv with >Hi
    icases Hi with (Hc | #Hc)
    · wp_apply_core wp_cmpxchg_suc c (null : Loc) null c _ _ rfl $$ Hc
      iintro Hc
      ipersist Hc
      imodintro
      isplitl []
      · inext; iright; iexact Hc
      wp_auto
      iapply HΦ
      itrivial
    · ihave %Hnn' := typedPointsto_not_null _ _ _ $$ Hc
      wp_apply_core wp_cmpxchg_fail c c null c DFrac.discard _ _ Hnn $$ Hc
      iintro _
      imodintro
      isplitl []
      · inext; iright; iexact Hc
      wp_auto
      -- second `uintptr(*c) != uintptr(unsafe.Pointer(c))`
      wp_apply_core wp_atomic_load _ _ c _ c $$ Hc
      iintro _
      wp_auto
      iapply HΦ
      itrivial
  · wp_apply_core wp_atomic_load _ _ c _ c $$ Hc
    iintro _
    imodintro
    isplitl []
    · inext; iright; iexact Hc
    wp_auto
    iapply HΦ
    itrivial

end proof

end Perennial
