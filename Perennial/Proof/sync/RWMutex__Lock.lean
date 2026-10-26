/-
The proof of `sync.(*RWMutex).Lock`.
-/
module

public import Perennial.Spec.sync.RWMutex__Lock
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.atomic.Int32__Add
public import Perennial.Spec.sync.runtime_SemacquireRWMutex

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem sync.rwmutex.RWMutex.Lock.wp_proof
    (wp_Mutex_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Int32_Add : sync.atomic.Int32.Add.spec (GF := GF) (hG := hG))
    (wp_runtime_SemacquireRWMutex : sync.runtime_SemacquireRWMutex.spec (GF := GF) (hG := hG)) :
    sync.rwmutex.RWMutex.Lock.spec (GF := GF) (hG := hG) := by
  intro γ rw N
  wp_start as #His
  simp only [isRWMutex_unseal, isRWMutexDef]
  iNamed His
  simp only [internal.race.Enabled, sync.rwmutexMaxReaders]
  wp_auto
  wp_apply wp_Mutex_Lock (RWW rw)
    (ghostVar γ.protGn.wlockGn (1 : Qp).half (WlockState.NotLocked (W32 0))) $$ [$Hmu]
    with ⟨Hmtx, Hwl⟩
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
  ihave X := step_Lock_readerCount_Add γ.protGn ws rs rc rwt state $$ [Hwl Hprot]
  · iframe
  imod X with X
  by_cases hz : rc = W32 0
  · -- fast path
    simp only [hz, ↓reduceIte]
    icases X with ⟨%Hst, Hwl_inv, Hprot⟩
    subst Hst
    imod fupd_mask_subseteq (mask_diff_ndot N "inv") with Hmask
    imod HΦ with ⟨%st, Hst, HΦ⟩
    simp only [ownRWMutex_unseal, ownRWMutexDef]
    icombine Hst Hstate gives % ⟨_, heq⟩
    subst heq
    imod ghostVar_update_halves rwmutex.Locked _ _ _ $$ Hst Hstate with ⟨Hst, Hstate⟩
    imod HΦ $$ [] Hst with HΦ
    · ipureintro; rfl
    imod Hmask with _
    imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hmtx Hwl_inv] with _
    · inext
      iexists ws, rs, (W32 0 + W32 (-rwmutexMaxReadersZ)), rwt, rwmutex.Locked
      simp only [rwLockedPart, named]
      iframe
    imodintro
    clear hz
    wp_auto
    iexact HΦ
  · -- slow path
    simp only [hz, ↓reduceIte]
    icases X with ⟨Hwl, Hprot⟩
    imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
    · inext
      iexists ws, rs, (rc + W32 (-rwmutexMaxReadersZ)), rwt, state
      iframe
    imodintro
    have hz' : ¬ (rc + W32 (-1073741824) + W32 1073741824 = W32 0) := by
      intro h; apply hz; word
    wp_auto
    wp_if_destruct
    · exfalso; apply hz; word
    wp_apply_core wp_Int32_Add $$ [] [-]
    · iPkgInit
    clear hz hz' Hif
    iinv Hinv with >Hi Hclose
    icases Hi with ⟨%ws, %rs, %rc', %rwt, %state, Hi⟩
    iNamed Hi
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists rwt
    iframe HreaderWait
    iintro HreaderWait
    imod Hmask with _
    ihave X := step_Lock_readerWait_Add γ.protGn (rc + W32 (-rwmutexMaxReadersZ) + W32 rwmutexMaxReadersZ)
      ws rs rc' rwt state $$ [Hwl Hprot]
    · iframe
    by_cases hz2 : sint.Z (rwt + (rc + W32 (-rwmutexMaxReadersZ) + W32 rwmutexMaxReadersZ)) = 0
    · -- got the lock
      simp only [hz2, ↓reduceIte]
      imod X with ⟨%Hst, Hwl_inv, Hprot⟩
      subst Hst
      imod fupd_mask_subseteq (mask_diff_ndot N "inv") with Hmask
      imod HΦ with ⟨%st, Hst, HΦ⟩
      simp only [ownRWMutex_unseal, ownRWMutexDef]
      icombine Hst Hstate gives % ⟨_, heq⟩
      subst heq
      imod ghostVar_update_halves rwmutex.Locked _ _ _ $$ Hst Hstate with ⟨Hst, Hstate⟩
      imod HΦ $$ [] Hst with HΦ
      · ipureintro; rfl
      imod Hmask with _
      imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hmtx Hwl_inv] with _
      · inext
        iexists ws, rs, rc', (rwt + (rc + W32 (-rwmutexMaxReadersZ) + W32 rwmutexMaxReadersZ)),
          rwmutex.Locked
        simp only [rwLockedPart, named]
        iframe
      imodintro
      have hz2' : rwt + (rc + W32 (-rwmutexMaxReadersZ) + W32 rwmutexMaxReadersZ) = W32 0 := by
        word
      clear hz2
      wp_auto
      wp_if_destruct
      · iexact HΦ
      · exfalso; exact Hif hz2'
    · -- wait for the remaining readers
      simp only [hz2, ↓reduceIte]
      imod X with ⟨Hwl, Hprot⟩
      imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
      · inext
        iexists ws, rs, rc', (rwt + (rc + W32 (-rwmutexMaxReadersZ) + W32 rwmutexMaxReadersZ)), state
        iframe
      imodintro
      wp_auto
      wp_if_destruct
      · exfalso; apply hz2; rw [Hif]; rfl
      · wp_apply_core wp_runtime_SemacquireRWMutex (RWWriterSem rw) γ.writerSemGn (N.@"sema")
          false (W64 0) $$ [] [-]
        · iframe #
        clear hz2 Hif
        iinv Hinv with >Hi Hclose <;> try exact ⟨mask_inv_sema N, trivial⟩
        icases Hi with ⟨%ws, %rs, %rc, %rwt, %state, Hi⟩
        iNamed Hi
        iapply fupd_mask_intro Std.LawfulSet.empty_subset
        iintro Hmask
        iexists ws
        iframe HwriterSem
        iintro %Hpos HwriterSem
        imod Hmask with _
        ihave Y := step_Lock_writerSem_Semacquire γ.protGn ws rs rc rwt state
          (by simp only [uint.nat] at Hpos; simp only [uint.Z]; omega) $$ [Hwl Hprot]
        · iframe
        imod Y with ⟨%Hst, Hwl_inv, Hprot⟩
        subst Hst
        imod fupd_mask_subseteq (mask_diff_ndot2 N "sema" "inv") with Hmask
        imod HΦ with ⟨%st, Hst, HΦ⟩
        simp only [ownRWMutex_unseal, ownRWMutexDef]
        icombine Hst Hstate gives % ⟨_, heq⟩
        subst heq
        imod ghostVar_update_halves rwmutex.Locked _ _ _ $$ Hst Hstate with ⟨Hst, Hstate⟩
        imod HΦ $$ [] Hst with HΦ
        · ipureintro; rfl
        imod Hmask with _
        imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hmtx Hwl_inv] with _
        · inext
          iexists (ws - W32 1), rs, rc, rwt, rwmutex.Locked
          simp only [rwLockedPart, named]
          iframe
        imodintro
        wp_auto
        iexact HΦ

end proof

end Perennial
