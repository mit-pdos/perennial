/-
The proof of `sync.(*RWMutex).TryRLock`.
-/
module

public import Perennial.Spec.sync.RWMutex__TryRLock
public import Perennial.Spec.sync.atomic.Int32__CompareAndSwap
public import Perennial.Spec.sync.atomic.Int32__Load

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

theorem sync.rwmutex.RWMutex.TryRLock.wp_proof
    (wp_Int32_Load : sync.atomic.Int32.Load.spec (GF := GF) (hG := hG))
    (wp_Int32_CompareAndSwap : sync.atomic.Int32.CompareAndSwap.spec (GF := GF) (hG := hG)) :
    sync.rwmutex.RWMutex.TryRLock.spec (GF := GF) (hG := hG) := by
  intro γ rw N
  wp_start as ⟨#His, Htok⟩
  simp only [isRWMutex_unseal, isRWMutexDef, ownRLockToken_unseal, ownRLockTokenDef]
  iNamed His
  simp only [internal.race.Enabled]
  wp_auto
  wp_for
  wp_apply_core wp_Int32_Load $$ [] [-]
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
  imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
  · inext
    iexists ws, rs, rc, rwt, state
    iframe
  imodintro
  wp_auto
  wp_if_destruct
  · wp_for_post
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  · wp_apply_core wp_Int32_CompareAndSwap $$ [] [-]
    · iPkgInit
    iinv Hinv with >Hi Hclose
    icases Hi with ⟨%ws, %rs, %rc', %rwt, %state, Hi⟩
    iNamed Hi
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists rc', (DFrac.own 1)
    iframe HreaderCount
    isplitr
    · ipureintro; split <;> rfl
    iintro HreaderCount
    by_cases hc : rc' = rc
    · subst hc
      simp only [↓reduceIte, decide_true]
      imod step_TryRLock_readerCount_CompareAndSwap γ.protGn ws rs rc' rwt state
        (by word) $$ [Htok Hprot] with ⟨%n, %Hst, Hprot⟩
      · iframe
      subst Hst
      imod Hmask with _
      icases HΦ with ⟨HΦ, -⟩
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
        iexists ws, rs, (rc' + W32 1), rwt, (rwmutex.RLocked (n + 1))
        simp only [rwLockedPart]
        iframe
      imodintro
      wp_auto
      wp_for_post
      iexact HΦ
    · simp only [hc, ↓reduceIte, decide_false]
      imod Hmask with _
      imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
      · inext
        iexists ws, rs, rc', rwt, state
        iframe
      imodintro
      wp_auto
      wp_for_post
      iframe

end proof

end Perennial
