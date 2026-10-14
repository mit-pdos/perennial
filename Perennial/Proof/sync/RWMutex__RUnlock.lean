/-
The proof of `sync.(*RWMutex).RUnlock`.
-/
module

public import Perennial.Spec.sync.RWMutex__RUnlock
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

set_option maxRecDepth 200000 in
theorem sync.rwmutex.RWMutex.RUnlock.wp_proof
    (wp_Int32_Add : sync.atomic.Int32.Add.spec (GF := GF) (hG := hG))
    (wp_runtime_Semrelease : sync.runtime_Semrelease.spec (GF := GF) (hG := hG)) :
    sync.rwmutex.RWMutex.RUnlock.spec (GF := GF) (hG := hG) := by
  intro γ rw N
  wp_start as #His
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
  imod fupd_mask_subseteq (mask_diff_ndot N "inv") with Hmask
  imod HΦ with ⟨%n, Hst, HΦ⟩
  simp only [ownRWMutex_unseal, ownRWMutexDef]
  icombine Hst Hstate gives % ⟨_, heq⟩
  subst heq
  imod ghostVar_update_halves (rwmutex.RLocked n) _ _ _ $$ Hst Hstate with ⟨Hst, Hstate⟩
  ihave X := step_RUnlock_readerCount_Add γ.protGn ws rs rc rwt n $$ Hprot
  imod X with X
  by_cases hneg : sint.Z (rc + W32 (-1)) < 0
  · simp only [hneg, ↓reduceIte]
    icases X with ⟨Hrtok, Hprot, Hwait_tok, %H1, %H2⟩
    imod HΦ $$ [Hst Hrtok] with HΦ
    · iframe
    imod Hmask with _
    imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
    · inext
      iexists ws, rs, (rc + W32 (-1)), rwt, (rwmutex.RLocked n)
      simp only [rwLockedPart]
      iframe
    imodintro
    wp_auto
    have h' : sint.Z (rc + W32 (-1)) < sint.Z (W32 0) := by word
    simp only [h', decide_true]
    wp_auto
    wp_method_call
    wp_auto
    have hA : ¬ (rc + W32 (-1) + W32 1 = W32 0) := by
      intro h; apply H1; simp only [rwmutexMaxReadersZ] at *; word
    simp only [hA, decide_false, sync.rwmutexMaxReaders]
    wp_auto
    have hB : ¬ (rc + W32 (-1) + W32 1 = W32 (-1073741824)) := by
      intro h; apply H2; simp only [rwmutexMaxReadersZ] at *; word
    simp only [hB, decide_false]
    wp_auto
    wp_apply_core wp_Int32_Add $$ [] [-]
    · iPkgInit
    clear hA hB h' hneg H1 H2
    iinv Hinv with >Hi Hclose
    icases Hi with ⟨%ws, %rs, %rc2, %rwt, %state, Hi⟩
    iNamed Hi
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists rwt
    iframe HreaderWait
    iintro HreaderWait
    imod Hmask with _
    ihave X := step_rUnlockSlow_readerWait_Add γ.protGn ws rs rc2 rwt state $$ [Hwait_tok Hprot]
    · iframe
    imod X with X
    by_cases hz : rwt + W32 (-1) = W32 0
    · simp only [hz, ↓reduceIte]
      icases X with ⟨Hprot, Hwtok⟩
      imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
      · inext
        iexists ws, rs, rc2, (W32 0), state
        iframe
      imodintro
      wp_auto
      wp_apply_core wp_runtime_Semrelease (RWWriterSem rw) γ.writerSemGn (N.@"sema")
        false (W64 1) $$ [] [-]
      · iframe #
      iinv Hinv with >Hi Hclose <;> try exact ⟨mask_inv_sema N, trivial⟩
      icases Hi with ⟨%ws2, %rs2, %rc3, %rwt2, %state2, Hi⟩
      iNamed Hi
      ihave Y := step_rUnlockSlow_writerSem_Semrelease γ.protGn ws2 rs2 rc3 rwt2 state2
        $$ [Hwtok Hprot]
      · iframe
      imod Y with Hprot
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hmask
      iexists ws2
      iframe HwriterSem
      iintro HwriterSem
      imod Hmask with _
      imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
      · inext
        iexists (ws2 + W32 1), rs2, rc3, rwt2, state2
        iframe
      imodintro
      wp_auto
      iexact HΦ
    · simp only [hz, ↓reduceIte]
      icases X with ⟨Hprot, -⟩
      imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
      · inext
        iexists ws, rs, rc2, (rwt + W32 (-1)), state
        iframe
      imodintro
      wp_auto
      simp only [hz, decide_false]
      wp_auto
      iexact HΦ
  · simp only [hneg, ↓reduceIte]
    icases X with ⟨Hrtok, Hprot, -⟩
    imod HΦ $$ [Hst Hrtok] with HΦ
    · iframe
    imod Hmask with _
    imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
    · inext
      iexists ws, rs, (rc + W32 (-1)), rwt, (rwmutex.RLocked n)
      simp only [rwLockedPart]
      iframe
    imodintro
    wp_auto
    have h' : ¬ (sint.Z (rc + W32 (-1)) < sint.Z (W32 0)) := by word
    simp only [h', decide_false]
    wp_auto
    iexact HΦ

end proof

end Perennial
