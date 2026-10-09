/-
`RWMutex.RLocker()`: the `Locker` whose `Lock`/`Unlock` are the `RWMutex`'s
`RLock`/`RUnlock` (`rlocker`), for the guarded spec of `rwmutex_guard`. Its `Lock`
needs a reader token (`ownRWMutex rw P`) and gives the read lock with `▷ P rfrac`, which
its `Unlock` gives back, so it is an `isLockerWith`, not an `isLocker`; `Cond.wp_Wait_with`
waits on a `Cond` over it.
-/
module

public import Perennial.Proof.sync_proof.cond
public import Perennial.Proof.sync_proof.rwmutex_guard

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace sync

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- The `Locker` interface value `rw.RLocker()` returns. -/
abbrev rlockerOf (rw : Loc) : GoInterfaceOk :=
  interface.mk (go.GoType.PointerType rlocker.ty) #rw

/-- `rw.RLocker()` is `Locker((*rlocker)(rw))`. -/
theorem RWMutex.wp_RLocker (rw : Loc) :
    {{ (True : IProp GF) }}
      (App (Val (rw @!! go.GoType.PointerType RWMutex.ty @!! go!"RLocker")) (Val #()))
    {{ RET #(GoInterface.ok (rlockerOf rw)); True }} := by
  wp_start
  wp_auto
  iapply HΦ; itrivial

/-- `(*rlocker)(rw).Lock()` is `rw.RLock()`. -/
theorem rlocker.wp_Lock (rw : Loc) (P : Qp → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownRWMutex rw P }}
      (App (Val (rw @!! go.GoType.PointerType rlocker.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); ownRWMutexRLocked rw P ∗ ▷ P rfrac }} := by
  wp_start as Hown
  wp_auto
  wp_apply RWMutex.wp_RLock $$ [$Hown] as ⟨Hl, HP⟩
  iapply HΦ
  iframe

/-- `(*rlocker)(rw).Unlock()` is `rw.RUnlock()`. -/
theorem rlocker.wp_Unlock (rw : Loc) (P : Qp → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownRWMutexRLocked rw P ∗ ▷ P rfrac }}
      (App (Val (rw @!! go.GoType.PointerType rlocker.ty @!! go!"Unlock")) (Val #()))
    {{ RET #(); ownRWMutex rw P }} := by
  wp_start as ⟨Hl, HP⟩
  wp_auto
  wp_apply RWMutex.wp_RUnlock $$ [$Hl $HP] as Hown
  iapply HΦ
  iframe

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

end wps

end sync

end Perennial
end
