/-
Port of `new/proof/sync_proof/mutex.v`: `sync.Mutex` (a `lock`) and the
`Locker` interface.
-/
import Perennial.Proof.sync_proof.base
import Perennial.Golang.Theory.Lock

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace sync

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

def isMutexDef (m : loc) (R : IProp GF) : IProp GF := isLock m R
/-- This means `m` is a valid mutex with invariant `R` (Rocq `Opaque isMutex`). -/
@[irreducible] def isMutex (m : loc) (R : IProp GF) : IProp GF := isMutexDef m R
theorem isMutex_unseal : @isMutex = @isMutexDef := by funext; with_unfolding_all rfl

def ownMutexDef (m : loc) : IProp GF := ownLock m
/-- This resource denotes ownership of the fact that the Mutex is currently
locked (Rocq `Opaque ownMutex`). -/
@[irreducible] def ownMutex (m : loc) : IProp GF := ownMutexDef m
theorem ownMutex_unseal : @ownMutex = @ownMutexDef := by funext; with_unfolding_all rfl

theorem ownMutex_exclusive (m : loc) : ⊢ ownMutex (GF := GF) m -∗ ownMutex m -∗ False := by
  simp only [ownMutex_unseal, ownMutexDef]
  exact ownLock_exclusive m

instance isMutex_ne (m : loc) : NonExpansive (isMutex (GF := GF) m) := by
  rw [isMutex_unseal]; unfold isMutexDef; infer_instance

instance isMutex_persistent (m : loc) (R : IProp GF) : Persistent (isMutex m R) := by
  rw [isMutex_unseal]; unfold isMutexDef; infer_instance

instance locked_timeless (m : loc) : Timeless (ownMutex (GF := GF) m) := by
  rw [ownMutex_unseal]; unfold ownMutexDef; infer_instance

theorem init_Mutex (R : IProp GF) (E : CoPset) (m : loc) :
    ⊢ typed_pointsto (GF := GF) m (zero_val sync.Mutex.t) (DFrac.own 1) -∗ ▷ R ={E}=∗
      isMutex m R := by
  simp only [isMutex_unseal, isMutexDef]
  exact init_lock R E m

theorem Mutex.wp_TryLock (m : loc) (R : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isMutex m R }}
      (App (Val (m @!! go.type.PointerType Mutex @!! go!"TryLock")) (Val #()))
    {{ (locked : Bool), RET #locked; if locked then ownMutex m ∗ R else True }} := by
  wp_start as #His
  simp only [isMutex_unseal, isMutexDef, ownMutex_unseal, ownMutexDef]
  wp_apply wp_lock_trylock $$ His as %locked H
  iapply HΦ $$ H

theorem Mutex.wp_Lock (m : loc) (R : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isMutex m R }}
      (App (Val (m @!! go.type.PointerType Mutex @!! go!"Lock")) (Val #()))
    {{ RET #(); ownMutex m ∗ R }} := by
  wp_start as #His
  simp only [isMutex_unseal, isMutexDef, ownMutex_unseal, ownMutexDef]
  wp_apply wp_lock_lock $$ His as ⟨Hown, HR⟩
  iapply HΦ
  iframe

/-- This form is useful for defer statements. -/
theorem Mutex.wp_Unlock (m : loc) (R : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isMutex m R ∗ ownMutex m ∗ ▷ R }}
      (App (Val (m @!! go.type.PointerType Mutex @!! go!"Unlock")) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#His, Hlocked, HR⟩
  simp only [isMutex_unseal, isMutexDef, ownMutex_unseal, ownMutexDef]
  wp_apply wp_lock_unlock $$ [$His $Hlocked $HR]
  iapply HΦ
  itrivial

/-- `i` implements `Locker` with `Lock` producing `P` and `Unlock` consuming it. -/
def isLocker (i : interface.t_ok) (P : IProp GF) : IProp GF :=
  iprop("#H_Lock" ∷ iprop({{ True }} (App (Val #(methods i.ty go!"Lock" i.v)) (Val #()))
      {{ RET #(); P }}) ∗
    "#H_Unlock" ∷ iprop({{ P }} (App (Val #(methods i.ty go!"Unlock" i.v)) (Val #()))
      {{ RET #(); True }}))

instance isLocker_persistent (v : interface.t_ok) (P : IProp GF) :
    Persistent (isLocker v P) := by
  unfold isLocker named; infer_instance

theorem Mutex_is_Locker (m : loc) (R : IProp GF) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.sync -∗ isMutex m R -∗
      isLocker (interface.mk (go.type.PointerType Mutex) #m) iprop(ownMutex m ∗ R) := by
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

end wps

end sync

end Perennial
end
