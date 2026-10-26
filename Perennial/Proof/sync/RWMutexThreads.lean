/-
`RWMutex` reader tokens paid for by **thread tokens**: the lock's reader tokens in a thread
pool (`threadPool`, `Perennial/Proof/ThreadPool.lean`), so that a reader holds a reader token
only inside its critical section and its thread token between them.

`RLock` takes a reader token, of which a lock has `actualMaxReaders` (`2^30 - 1`), the
bound below which its reader counter does not overflow. A goroutine (or an object) that keeps
a reader token for its whole life and is then abandoned, never joined, takes the token with
it, and a program that does so without bound runs out of them, although Go counts only the
readers inside `RLock`..`RUnlock` at one time. What bounds those is that each is a live
thread: with `threadBound GF ≤ 2 ^ 30`, putting the tokens in a thread pool lets each
thread borrow one for a critical section with its thread token (`threadPool.borrow*`) and
give it back after `RUnlock` (`threadPool.giveBack`), so the stock never runs out.

* `rwmutex.init_RWMutex_threadPool`: `rwmutex.init_RWMutex`, with every reader token in a pool
  (`threadPool.isThreadPool Np γp (rwmutex.ownRLockToken γ)`; the token is timeless, so
  `threadPool.borrow_timeless` applies).
* `init_RWMutex_threadPool`: the guarded interface's `init_RWMutex`, with every reader token
  (`ownRWMutex rw P`) in a pool, and the persistent guard `isRWMutexGuard rw P` for the writers
  (`RWMutex.wp_Lock_guard`). `ownRWMutex rw P` is not timeless: borrow it with a later credit
  (`threadPool.borrow_lc`) or where a later is stripped.

A pool can also be made from some of the tokens only (`threadPool.init`), the others used as
before. A thread borrows one token at a time per thread token it holds, so this pays for one
read lock at a time per thread; a thread holding the read locks of two `RWMutex`es at once
pays for the other one with a reader token, as before.
-/
module

public import Perennial.Proof.sync.RWMutexGuard
public import Perennial.Proof.ThreadPool

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace sync

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem threadBound_le_actualMaxReaders (Hb : threadBound GF ≤ 2 ^ 30) :
    threadBound GF ≤ Int.toNat rwmutex.actualMaxReaders + 1 := by
  rw [rwmutex.actualMaxReaders_unseal]; omega

namespace rwmutex

instance ownRLockToken_timeless (γ : RWMutexNames) : Timeless (ownRLockToken (GF := GF) γ) := by
  rw [ownRLockToken_unseal]; unfold ownRLockTokenDef; infer_instance

/-- `init_RWMutex`, with every reader token in a thread pool of namespace `Np`. -/
theorem init_RWMutex_threadPool {E : CoPset} (N Np : Namespace) (rw : Loc)
    (Hb : threadBound GF ≤ 2 ^ 30) :
    typedPointsto (GF := GF) rw (zero_val RWMutex) (DFrac.own 1) ⊢
    |={E}=> ∃ (γ : RWMutexNames) (γp : GName), isRWMutex rw γ N ∗ ownRWMutex γ (.RLocked 0) ∗
      threadPool.isThreadPool Np γp (ownRLockToken γ) := by
  iintro Hrw
  imod init_RWMutex (E := E) N rw $$ Hrw with ⟨%γ, #His, Hst, Htoks⟩
  imod threadPool.init Np (ownRLockToken γ) E _ (threadBound_le_actualMaxReaders Hb) $$ Htoks
    with ⟨%γp, #Hpool⟩
  imodintro
  iexists γ, γp
  iframe
  iframe #

end rwmutex

/-- A guarded reader token gives the persistent guard. -/
theorem ownRWMutex_isRWMutexGuard (rw : Loc) (P : Qp → IProp GF) :
    ownRWMutex rw P ⊢ isRWMutexGuard rw P := by
  simp only [ownRWMutex_unseal, ownRWMutexDef, isRWMutexGuard_unseal, isRWMutexGuardDef]
  iintro ⟨%γ, %γmax, %γrlocked, %γlocked, H⟩
  iNamed H
  iexists γ, γmax, γrlocked, γlocked
  iframe #

/-- The guarded `init_RWMutex`, with every reader token in a thread pool of namespace `Np`, and
the guard for the writers. -/
theorem init_RWMutex_threadPool (P : Qp → IProp GF) {E : CoPset} (Np : Namespace) (rw : Loc)
    [HPfrac : Fractional P] (Hb : threadBound GF ≤ 2 ^ 30) :
    ⊢ ▷ P 1 -∗ typedPointsto (GF := GF) rw (zero_val RWMutex) (DFrac.own 1) ={E}=∗
      ∃ γp : GName, isRWMutexGuard rw P ∗ threadPool.isThreadPool Np γp (ownRWMutex rw P) := by
  iintro HP Hrw
  imod init_RWMutex P (E := E) rw $$ HP Hrw with Htoks
  obtain ⟨n, hn⟩ : ∃ n, Int.toNat rwmutex.actualMaxReaders = n + 1 :=
    ⟨Int.toNat rwmutex.actualMaxReaders - 1, by have := actualMaxReaders_ge_2; omega⟩
  rw [hn]
  simp only [List.replicate]
  icases Htoks with ⟨Htok, Htoks⟩
  icases persistent_entails_left (ownRWMutex_isRWMutexGuard rw P) $$ Htok with ⟨Htok, #Hguard⟩
  imod threadPool.init Np (ownRWMutex rw P) E (n + 1)
    (by have := threadBound_le_actualMaxReaders Hb; omega) $$ [Htok Htoks] with ⟨%γp, #Hpool⟩
  · simp only [List.replicate]
    iframe
  imodintro
  iexists γp
  iframe #

end wps

end sync

end Perennial
