/-
What is derived from the linked results of `sync` and is not a Go function's triple: the
`Locker` instances (`Mutex_is_Locker`, `rlocker_isLockerWith`), the variant
`Cond.wp_Wait_with` of `Cond.Wait`'s spec, the guarded `RWMutex` specs (`sync.RWMutex.wp_RLock`,
..., corollaries of the low-level `sync.rwmutex.RWMutex.wp_RLock`, ...) and the specs of the
`WaitGroup` "join" idiom (`sync.join.WaitGroup.wp_Add`, ...) and of its thread-token variant
(`sync.tokJoin.WaitGroup.wp_Add`, ...).
-/
module

public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.RWMutexGuard
public import Perennial.Proof.sync.WaitGroupJoin
public import Perennial.Proof.sync.WaitGroupTokJoin

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace sync

section results
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem Mutex_is_Locker (m : Loc) (R : IProp GF) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.sync -∗ isMutex m R -∗
      isLocker (interface.mk (go.GoType.PointerType Mutex.ty) #m) iprop(ownMutex m ∗ R) := by
  iintro #Hi #Hm
  unfold isLocker
  isplitl
  · imodintro
    iintro %Φ _ HΦ
    wp_apply Mutex.wp_Lock $$ [$Hm] with H
    iapply HΦ $$ H
  · imodintro
    iintro %Φ ⟨Hown, HR⟩ HΦ
    wp_apply Mutex.wp_Unlock $$ [$Hm $Hown $HR]
    iapply HΦ
    itrivial


/-- `Wait` on a condition variable whose locker's `Lock` needs a resource `Pre` that its
`Unlock` gives back (`isLockerWith`), such as `rw.RLocker()` (`rlocker_isLockerWith`). -/
theorem Cond.wp_Wait_with (c : Loc) (m : GoInterfaceOk) (Pre R : IProp GF) :
    {{ isCond c m ∗ isLockerWith m Pre R ∗ R }}
      (App (Val (c @!! go.GoType.PointerType Cond.ty @!! go!"Wait")) (Val #()))
    {{ RET #(); R }} := by
  wp_start as ⟨H, #Hlock, HR⟩
  simp only [isCond_unseal, isCondDef]
  iNamed H
  wp_auto
  wp_apply copyChecker.wp_check $$ [$Hchecker]
  wp_apply wp_runtime_notifyListAdd $$ [$Hnotify] with %x _
  unfold isLockerWith
  iNamed Hlock
  wp_apply H_Unlock $$ HR as HPre
  wp_apply wp_runtime_notifyListWait $$ [$Hnotify] with _
  wp_apply H_Lock $$ HPre with HR
  wp_end

theorem RWMutex.wp_RLock (rw : Loc) (P : Qp → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownRWMutex rw P }}
      (App (Val (rw @!! go.GoType.PointerType RWMutex.ty @!! go!"RLock")) (Val #()))
    {{ RET #(); ownRWMutexRLocked rw P ∗ ▷ P rfrac }} :=
  RWMutex.wp_RLock_of rwmutex.RWMutex.wp_RLock rw P

theorem RWMutex.wp_RUnlock (rw : Loc) (P : Qp → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownRWMutexRLocked rw P ∗ ▷ P rfrac }}
      (App (Val (rw @!! go.GoType.PointerType RWMutex.ty @!! go!"RUnlock")) (Val #()))
    {{ RET #(); ownRWMutex rw P }} :=
  RWMutex.wp_RUnlock_of rwmutex.RWMutex.wp_RUnlock rw P

theorem RWMutex.wp_Lock (rw : Loc) (P : Qp → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownRWMutex rw P }}
      (App (Val (rw @!! go.GoType.PointerType RWMutex.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); ownRWMutexLocked rw P ∗ ▷ P 1 }} :=
  RWMutex.wp_Lock_of rwmutex.RWMutex.wp_Lock rw P

theorem RWMutex.wp_Unlock (rw : Loc) (P : Qp → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownRWMutexLocked rw P ∗ ▷ P 1 }}
      (App (Val (rw @!! go.GoType.PointerType RWMutex.ty @!! go!"Unlock")) (Val #()))
    {{ RET #(); ownRWMutex rw P }} :=
  RWMutex.wp_Unlock_of rwmutex.RWMutex.wp_Unlock rw P

/-- `Lock` by a writer holding only the guard. -/
theorem RWMutex.wp_Lock_guard (rw : Loc) (P : Qp → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isRWMutexGuard rw P }}
      (App (Val (rw @!! go.GoType.PointerType RWMutex.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); ownRWMutexWLocked rw P ∗ ▷ P 1 }} :=
  RWMutex.wp_Lock_guard_of rwmutex.RWMutex.wp_Lock rw P

/-- `Unlock` by a writer that locked through the guard. -/
theorem RWMutex.wp_Unlock_guard (rw : Loc) (P : Qp → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownRWMutexWLocked rw P ∗ ▷ P 1 }}
      (App (Val (rw @!! go.GoType.PointerType RWMutex.ty @!! go!"Unlock")) (Val #()))
    {{ RET #(); True }} :=
  RWMutex.wp_Unlock_guard_of rwmutex.RWMutex.wp_Unlock rw P

/-- `rw.RLocker()` is a locker whose `Lock` takes a reader token and gives the read lock. -/
theorem rlocker_isLockerWith (rw : Loc) (P : Qp → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.sync ⊢
      isLockerWith (rlockerOf rw) (ownRWMutex rw P) iprop(ownRWMutexRLocked rw P ∗ ▷ P rfrac) := by
  iintro #Hi
  unfold isLockerWith
  isplitl
  · imodintro
    iintro %Φ Hown HΦ
    wp_apply rlocker.wp_Lock rw P $$ [$Hi $Hown] as H
    iapply HΦ $$ H
  · imodintro
    iintro %Φ ⟨Hl, HP⟩ HΦ
    wp_apply rlocker.wp_Unlock rw P $$ [$Hi $Hl $HP] as H
    iapply HΦ $$ H


end results

namespace join

section waitgroup_join_idiom
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem WaitGroup.wp_Add (P' : IProp GF) (wg : Loc) (P : IProp GF) (num_added : w32) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownAdder wg num_added P ∗
        ⌜sint.Z num_added < 2 ^ 31 - 1⌝ }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Add")) (Val #(W64 1)))
    {{ RET #(); ownAdder wg (num_added + W32 1) iprop(P ∗ P') ∗ ownDone wg P' }} :=
  WaitGroup.wp_Add_of sync.WaitGroup.wp_Add P' wg P num_added

theorem WaitGroup.wp_Done (P : IProp GF) (wg : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownDone wg P ∗ P }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Done")) (Val #()))
    {{ RET #(); True }} :=
  WaitGroup.wp_Done_of sync.WaitGroup.wp_Done P wg

theorem WaitGroup.wp_Wait (P : IProp GF) (n : w32) (wg : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownAdder wg n P }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Wait")) (Val #()))
    {{ RET #(); ▷ P ∗ ownAdder wg (W32 0) iprop(True) }} :=
  WaitGroup.wp_Wait_of sync.WaitGroup.wp_Wait P n wg

end waitgroup_join_idiom

end join

namespace tokJoin

section waitgroup_tok_join_idiom
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem WaitGroup.wp_Add (P' : IProp GF) (N : Namespace) (L : IProp GF) [Timeless L] (wg : Loc)
    (n : Nat) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownAdder N L wg n P ∗ threadTok }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Add")) (Val #(W64 1)))
    {{ RET #(); ownAdder N L wg (n + 1) iprop(P ∗ P') ∗ ownDone N L wg P' }} :=
  WaitGroup.wp_Add_of sync.WaitGroup.wp_Add P' N L wg n P

theorem WaitGroup.wp_Done (N : Namespace) (L : IProp GF) (wg : Loc) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownDone N L wg P ∗ P }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Done")) (Val #()))
    {{ RET #(); threadTok }} :=
  WaitGroup.wp_Done_of sync.WaitGroup.wp_Done N L wg P

theorem WaitGroup.wp_Wait (N : Namespace) (L : IProp GF) (wg : Loc) (n : Nat) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownAdder N L wg n P }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Wait")) (Val #()))
    {{ RET #(); ▷ P ∗ ownAdder N L wg 0 iprop(True) }} :=
  WaitGroup.wp_Wait_of sync.WaitGroup.wp_Wait N L wg n P

end waitgroup_tok_join_idiom

end tokJoin

end sync

end Perennial
