/-
The proof of `sync.(*RWMutex).TryLock`.
-/
module

public import Perennial.Spec.sync.RWMutex__TryLock
public import Perennial.Spec.sync.Mutex__TryLock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Spec.sync.atomic.Int32__CompareAndSwap

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

theorem sync.rwmutex.RWMutex.TryLock.wp_proof
    (wp_Mutex_TryLock : sync.Mutex.TryLock.spec (GF := GF) (hG := hG))
    (wp_Int32_CompareAndSwap : sync.atomic.Int32.CompareAndSwap.spec (GF := GF) (hG := hG))
    (wp_Mutex_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    sync.rwmutex.RWMutex.TryLock.spec (GF := GF) (hG := hG) := by
  intro γ rw N
  wp_start as #His
  simp only [isRWMutex_unseal, isRWMutexDef]
  iNamed His
  simp only [internal.race.Enabled, sync.rwmutexMaxReaders]
  wp_auto
  wp_apply wp_Mutex_TryLock (RWW rw)
    (ghostVar γ.protGn.wlockGn (1 : Qp).half (WlockState.NotLocked (W32 0))) $$ [$Hmu]
    with %locked Hl
  cases locked
  · simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  · simp only [↓reduceIte]
    icases Hl with ⟨Hmtx, Hwl⟩
    wp_auto
    wp_apply_core wp_Int32_CompareAndSwap $$ [] [-]
    · iPkgInit
    iinv Hinv with >Hi Hclose
    icases Hi with ⟨%ws, %rs, %rc, %rwt, %state, Hi⟩
    iNamed Hi
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists rc, (DFrac.own 1)
    iframe HreaderCount
    isplitr
    · ipureintro; split <;> rfl
    iintro HreaderCount
    by_cases hc : rc = W32 0
    · subst hc
      simp only [↓reduceIte, decide_true]
      ihave X := step_TryLock_readerCount_CompareAndSwap γ.protGn ws rs (W32 0) rwt state rfl
        $$ [Hwl Hprot]
      · iframe
      imod X with ⟨%Hst, Hwl_inv, Hprot⟩
      subst Hst
      imod Hmask with _
      icases HΦ with ⟨HΦ, -⟩
      imod fupd_mask_subseteq (mask_diff_ndot N "inv") with Hmask
      imod HΦ with ⟨%st, Hst, HΦ⟩
      simp only [ownRWMutex_unseal, ownRWMutexDef]
      icombine Hst Hstate gives % ⟨_, heq⟩
      subst heq
      imod ghostVar_update_halves rwmutex.Locked _ _ _ $$ Hst Hstate with ⟨Hst, Hstate⟩
      imod HΦ $$ [] Hst with HΦ
      · ipureintro; rfl
      imod Hmask with _
      have e : W32 0 + W32 (-rwmutexMaxReadersZ) = (W32 (-1073741824) : w32) := by
        simp only [rwmutexMaxReadersZ]; word
      rw [e]
      imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hmtx Hwl_inv] with _
      · inext
        iexists ws, rs, (W32 (-1073741824)), rwt, rwmutex.Locked
        simp only [rwLockedPart, named]
        iframe
      imodintro
      wp_auto
      iexact HΦ
    · simp only [hc, ↓reduceIte, decide_false]
      imod Hmask with _
      imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
      · inext
        iexists ws, rs, rc, rwt, state
        iframe
      imodintro
      clear hc
      wp_auto
      wp_apply wp_Mutex_Unlock (RWW rw)
        (ghostVar γ.protGn.wlockGn (1 : Qp).half (WlockState.NotLocked (W32 0)))
        $$ [$Hmu $Hmtx $Hwl]
      icases HΦ with ⟨-, HΦ⟩
      iexact HΦ

end proof

end Perennial
