/-
The proof of `sync.(*RWMutex).RLock`.
-/
module

public import Perennial.Spec.sync.RWMutex__RLock
public import Perennial.Spec.sync.atomic.Int32__Add
public import Perennial.Spec.sync.runtime_SemacquireRWMutexR

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem sync.rwmutex.RWMutex.RLock.wp_proof
    (wp_Int32_Add : sync.atomic.Int32.Add.spec (GF := GF) (hG := hG))
    (wp_runtime_SemacquireRWMutexR : sync.runtime_SemacquireRWMutexR.spec (GF := GF) (hG := hG)) :
    sync.rwmutex.RWMutex.RLock.spec (GF := GF) (hG := hG) := by
  intro γ rw N
  wp_start as ⟨#His, Htok⟩
  simp only [isRWMutex_unseal, isRWMutexDef, ownRLockToken_unseal, ownRLockTokenDef]
  iNamed His
  simp only [internal.race.Enabled]
  wp_auto
  wp_apply_core wp_Int32_Add $$ [] [-]
  · iPkgInit
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%ws, %rs, %rc, %rwt, %state, Hi⟩
  iNamed Hi
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists rc
  iframe HreaderCount
  iintro HreaderCount
  imod Hmask with _
  imod step_RLock_readerCount_Add γ.protGn ws rs rc rwt state $$ [Htok Hprot] with Hprot_inv
  · iframe
  by_cases h : 0 ≤ sint.Z (rc + W32 1)
  · -- fast path
    simp only [h, ↓reduceIte]
    icases Hprot_inv with ⟨%n, %Hst, Hprot⟩
    subst Hst
    imod fupd_mask_subseteq (mask_diff_ndot N "inv") with Hmask
    imod HΦ with ⟨%st, Hst, HΦ⟩
    simp only [ownRWMutex_unseal, ownRWMutexDef]
    icombine Hst Hstate gives % ⟨_, heq⟩
    subst heq
    imod ghostVar_update_halves (rwmutex.RLocked (n + 1)) _ _ _ $$ Hst Hstate with ⟨Hst, Hstate⟩
    imod HΦ $$ %n [] Hst with HΦ
    · ipureintro; rfl
    imod Hmask with _
    imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
    · inext
      iexists ws, rs, (rc + W32 1), rwt, (rwmutex.RLocked (n + 1))
      simp only [rwLockedPart]
      iframe
    imodintro
    wp_auto
    have h' : ¬ (sint.Z (rc + W32 1) < sint.Z (W32 0)) := by word
    simp only [h', decide_false]
    wp_auto
    iexact HΦ
  · -- slow path
    simp only [h, ↓reduceIte]
    iNamed Hprot_inv
    imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot_inv Hlocked] with _
    · inext
      iexists ws, rs, (rc + W32 1), rwt, state
      iframe
    imodintro
    wp_auto
    have h' : sint.Z (rc + W32 1) < sint.Z (W32 0) := by word
    simp only [h', decide_true]
    wp_auto
    wp_apply_core wp_runtime_SemacquireRWMutexR (RWReaderSem rw) γ.readerSemGn (N.@"sema")
      false (W64 0) $$ [] [-]
    · iframe #
    iinv Hinv with >Hi Hclose <;> try exact ⟨mask_inv_sema N, trivial⟩
    icases Hi with ⟨%ws, %rs, %rc, %rwt, %state, Hi⟩
    iNamed Hi
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    iexists rs
    iframe HreaderSem
    iintro %Hpos HreaderSem
    imod Hmask with _
    imod step_RLock_readerSem_Semacquire γ.protGn ws rs rc rwt state
      (by simp only [uint.nat] at Hpos; simp only [uint.Z]; omega) $$ Hprot with ⟨%n, %Hst, Hprot⟩
    subst Hst
    imod fupd_mask_subseteq (mask_diff_ndot2 N "sema" "inv") with Hmask
    imod HΦ with ⟨%st, Hst, HΦ⟩
    simp only [ownRWMutex_unseal, ownRWMutexDef]
    icombine Hst Hstate gives % ⟨_, heq⟩
    subst heq
    imod ghostVar_update_halves (rwmutex.RLocked (n + 1)) _ _ _ $$ Hst Hstate with ⟨Hst, Hstate⟩
    imod HΦ $$ %n [] Hst with HΦ
    · ipureintro; rfl
    imod Hmask with _
    imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
    · inext
      iexists ws, (rs - W32 1), rc, rwt, (rwmutex.RLocked (n + 1))
      simp only [rwLockedPart]
      iframe
    imodintro
    wp_auto
    iexact HΦ

end proof

end Perennial
