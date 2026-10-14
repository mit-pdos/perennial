/-
The proof of `sync.(*RWMutex).Unlock`.
-/
module

public import Perennial.Spec.sync.RWMutex__Unlock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Spec.sync.atomic.Int32__Add
public import Perennial.Spec.sync.runtime_Semrelease

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

theorem sync.rwmutex.RWMutex.Unlock.wp_proof
    (wp_Int32_Add : sync.atomic.Int32.Add.spec (GF := GF) (hG := hG))
    (wp_runtime_Semrelease : sync.runtime_Semrelease.spec (GF := GF) (hG := hG))
    (wp_Mutex_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    sync.rwmutex.RWMutex.Unlock.spec (GF := GF) (hG := hG) := by
  intro γ rw N
  wp_start as #His
  simp only [isRWMutex_unseal, isRWMutexDef]
  iNamed His
  simp only [internal.race.Enabled, sync.rwmutexMaxReaders]
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
  imod Hmask with -
  imod fupd_mask_subseteq (mask_diff_ndot N "inv") with Hmask
  imod HΦ with ⟨Hst, HΦ⟩
  simp only [ownRWMutex_unseal, ownRWMutexDef]
  icombine Hst Hstate gives % ⟨_, heq⟩
  subst heq
  imod ghostVar_update_halves (rwmutex.RLocked 0) _ _ _ $$ Hst Hstate with ⟨Hst, Hstate⟩
  imod HΦ $$ Hst with HΦ
  imod Hmask with -
  simp only [rwLockedPart]
  icases Hlocked with ⟨Hmtx, Hwl_in⟩
  ihave X := step_Unlock_readerCount_Add γ.protGn ws rs rc rwt $$ [Hwl_in Hprot]
  · iframe
  imod X with ⟨Hwl, Hprot, %Hr1, %Hr2⟩
  imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot] with -
  · inext
    iexists ws, rs, (rc + W32 rwmutexMaxReadersZ), rwt, (rwmutex.RLocked 0)
    simp only [rwLockedPart]
    iframe
  imodintro
  wp_auto
  wp_if_destruct
  · exfalso; simp only [rwmutexMaxReadersZ] at *; word
  ihave HI : iprop(∃ (i : w64) (r2 : w32), "i" ∷ i_ptr ↦ i ∗
      "Hwl" ∷ ghostVar γ.protGn.wlockGn (1 : Qp).half (WlockState.NotLocked r2) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z (rc + W32 rwmutexMaxReadersZ)⌝ ∗
      "%Hrr" ∷ ⌜sint.Z r2 = sint.Z (rc + W32 rwmutexMaxReadersZ) - sint.Z i⌝) $$ [i Hwl]
  · iexists (W64 0), (rc + W32 rwmutexMaxReadersZ)
    iframe
    ipureintro; simp only [rwmutexMaxReadersZ] at *; and_intros <;> word
  wp_for HI
  split
  · rename_i hlt
    simp only [decide_eq_true_eq, sext_32_64] at hlt
    wp_auto
    wp_apply_core wp_runtime_Semrelease (RWReaderSem rw) γ.readerSemGn (N.@"sema")
      false (W64 0) $$ [] [-]
    · iframe #
    have hpos : 0 < sint.Z r2 := by simp only [rwmutexMaxReadersZ] at *; word
    have hfin : (0 ≤ sint.Z (i + W64 1) ∧ sint.Z (i + W64 1) ≤ sint.Z (rc + W32 rwmutexMaxReadersZ)) ∧
        sint.Z (r2 - W32 1) = sint.Z (rc + W32 rwmutexMaxReadersZ) - sint.Z (i + W64 1) := by
      simp only [rwmutexMaxReadersZ] at *; and_intros <;> word
    clear Hif hlt Hr1 Hr2 Hi Hrr
    iinv Hinv with >Hi2 Hclose <;> try exact ⟨mask_inv_sema N, trivial⟩
    icases Hi2 with ⟨%ws, %rs, %rc', %rwt, %state, Hi2⟩
    iNamed Hi2
    ihave X := step_Unlock_readerSem_Semrelease γ.protGn ws rs rc' rwt r2 state hpos $$ [Hwl Hprot]
    · iframe
    imod X with ⟨Hwl, Hprot⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    iexists rs
    iframe HreaderSem
    iintro HreaderSem
    imod Hmask with -
    imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with -
    · inext
      iexists ws, (rs + W32 1), rc', rwt, state
      iframe
    imodintro
    wp_auto
    wp_for_post
    iframe
    iexists (i + W64 1), (r2 - W32 1)
    iframe
    ipureintro; exact hfin
  · rename_i hlt
    simp only [decide_eq_true_eq, sext_32_64] at hlt
    have hr0 : r2 = W32 0 := by simp only [rwmutexMaxReadersZ] at *; word
    subst hr0
    wp_auto
    wp_apply wp_Mutex_Unlock (RWW rw)
      (ghostVar γ.protGn.wlockGn (1 : Qp).half (WlockState.NotLocked (W32 0)))
      $$ [$Hmu $Hmtx $Hwl]
    iexact HΦ

end proof

end Perennial
