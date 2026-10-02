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

def is_Mutex_def (m : loc) (R : IProp GF) : IProp GF := is_lock m R
/-- This means `m` is a valid mutex with invariant `R` (Rocq `Opaque is_Mutex`). -/
@[irreducible] def is_Mutex (m : loc) (R : IProp GF) : IProp GF := is_Mutex_def m R
theorem is_Mutex_unseal : @is_Mutex = @is_Mutex_def := by funext; with_unfolding_all rfl

def own_Mutex_def (m : loc) : IProp GF := own_lock m
/-- This resource denotes ownership of the fact that the Mutex is currently
locked (Rocq `Opaque own_Mutex`). -/
@[irreducible] def own_Mutex (m : loc) : IProp GF := own_Mutex_def m
theorem own_Mutex_unseal : @own_Mutex = @own_Mutex_def := by funext; with_unfolding_all rfl

theorem own_Mutex_exclusive (m : loc) : ⊢ own_Mutex (GF := GF) m -∗ own_Mutex m -∗ False := by
  simp only [own_Mutex_unseal, own_Mutex_def]
  exact own_lock_exclusive m

instance is_Mutex_ne (m : loc) : NonExpansive (is_Mutex (GF := GF) m) := by
  rw [is_Mutex_unseal]; unfold is_Mutex_def; infer_instance

instance is_Mutex_persistent (m : loc) (R : IProp GF) : Persistent (is_Mutex m R) := by
  rw [is_Mutex_unseal]; unfold is_Mutex_def; infer_instance

instance locked_timeless (m : loc) : Timeless (own_Mutex (GF := GF) m) := by
  rw [own_Mutex_unseal]; unfold own_Mutex_def; infer_instance

theorem init_Mutex (R : IProp GF) (E : CoPset) (m : loc) :
    ⊢ typed_pointsto (GF := GF) m (zero_val sync.Mutex.t) (DFrac.own 1) -∗ ▷ R ={E}=∗
      is_Mutex m R := by
  simp only [is_Mutex_unseal, is_Mutex_def]
  exact init_lock R E m

theorem wp_Mutex__TryLock (m : loc) (R : IProp GF) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ is_Mutex m R }}
      (App (Val (m @!! go.type.PointerType Mutex @!! go!"TryLock")) (Val #()))
    {{ (locked : Bool), RET #locked; if locked then own_Mutex m ∗ R else True }} := by
  wp_start as #His
  simp only [is_Mutex_unseal, is_Mutex_def, own_Mutex_unseal, own_Mutex_def]
  wp_apply wp_lock_trylock $$ His as %locked H
  iapply HΦ $$ H

theorem wp_Mutex__Lock (m : loc) (R : IProp GF) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ is_Mutex m R }}
      (App (Val (m @!! go.type.PointerType Mutex @!! go!"Lock")) (Val #()))
    {{ RET #(); own_Mutex m ∗ R }} := by
  wp_start as #His
  simp only [is_Mutex_unseal, is_Mutex_def, own_Mutex_unseal, own_Mutex_def]
  wp_apply wp_lock_lock $$ His as ⟨Hown, HR⟩
  iapply HΦ
  iframe

/-- This form is useful for defer statements. -/
theorem wp_Mutex__Unlock (m : loc) (R : IProp GF) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ is_Mutex m R ∗ own_Mutex m ∗ ▷ R }}
      (App (Val (m @!! go.type.PointerType Mutex @!! go!"Unlock")) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#His, Hlocked, HR⟩
  simp only [is_Mutex_unseal, is_Mutex_def, own_Mutex_unseal, own_Mutex_def]
  wp_apply wp_lock_unlock $$ [$His $Hlocked $HR]
  iapply HΦ
  itrivial

/-- `i` implements `Locker` with `Lock` producing `P` and `Unlock` consuming it. -/
def is_Locker (i : interface.t_ok) (P : IProp GF) : IProp GF :=
  iprop("#H_Lock" ∷ iprop({{ True }} (App (Val #(methods i.ty go!"Lock" i.v)) (Val #()))
      {{ RET #(); P }}) ∗
    "#H_Unlock" ∷ iprop({{ P }} (App (Val #(methods i.ty go!"Unlock" i.v)) (Val #()))
      {{ RET #(); True }}))

instance is_Locker_persistent (v : interface.t_ok) (P : IProp GF) :
    Persistent (is_Locker v P) := by
  unfold is_Locker named; infer_instance

theorem Mutex_is_Locker (m : loc) (R : IProp GF) :
    ⊢ is_pkg_init (PROP := IProp GF) pkg_id.sync -∗ is_Mutex m R -∗
      is_Locker (interface.mk (go.type.PointerType Mutex) #m) iprop(own_Mutex m ∗ R) := by
  iintro #Hi #Hm
  unfold is_Locker
  isplitl
  · imodintro
    iintro %Φ _ HΦ
    wp_apply wp_Mutex__Lock $$ [$Hm] with H
    iapply HΦ $$ H
  · imodintro
    iintro %Φ ⟨Hown, HR⟩ HΦ
    wp_apply wp_Mutex__Unlock $$ [$Hm $Hown $HR]
    iapply HΦ
    itrivial

end wps

end sync

end Perennial
end
