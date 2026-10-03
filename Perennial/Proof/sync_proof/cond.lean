/-
Port of `new/proof/sync_proof/cond.v`: `sync.Cond`.
-/
import Perennial.Proof.sync_proof.base
import Perennial.Proof.sync_proof.mutex

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

/-- This means `c` is a condvar with underlying Locker `m`. -/
def is_Cond_def (c : loc) (m : interface.t_ok) : IProp GF :=
  iprop("#Hi" ∷ is_pkg_init (PROP := IProp GF) pkg_id.sync ∗
    "#Hc" ∷ typed_pointsto (struct_field_ref Cond.t go!"L" c) (interface.ok m) DFrac.discard ∗
    -- FIXME (Rocq): not accurate to assume it never changes, there should be an
    -- unknown notifyList struct in an invariant
    "#Hnotify" ∷ typed_pointsto (struct_field_ref Cond.t go!"notify" c)
      (zero_val notifyList.t) DFrac.discard ∗
    "#Hchecker" ∷ typed_pointsto (struct_field_ref Cond.t go!"checker" c)
      (zero_val copyChecker.t) DFrac.discard)
@[irreducible] def is_Cond (c : loc) (m : interface.t_ok) : IProp GF := is_Cond_def c m
theorem is_Cond_unseal : @is_Cond = @is_Cond_def := by funext; with_unfolding_all rfl

instance is_Cond_persistent (c : loc) (m : interface.t_ok) : Persistent (is_Cond (GF := GF) c m) := by
  rw [is_Cond_unseal]; unfold is_Cond_def named; infer_instance

theorem wp_NewCond (m : interface.t_ok) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.sync }}
      (App (Val (@! NewCond)) (Val #(interface.ok m)))
    {{ (c : loc), RET #c; is_Cond c m }} := by
  wp_start as _
  wp_auto
  wp_pures
  wp_alloc c as Hc
  iStructNamed Hc
  ipersist L
  ipersist notify
  ipersist checker
  wp_pures
  iapply HΦ
  rw [is_Cond_unseal]; unfold is_Cond_def
  iframe #
  done

theorem wp_copyChecker__check (c : loc) (c_v : copyChecker.t) (dq : DFrac) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ typed_pointsto (GF := GF) c c_v dq }}
      (App (Val (c @!! go.type.PointerType copyChecker @!! go!"check")) (Val #()))
    {{ RET #(); typed_pointsto (GF := GF) c c_v dq }} := by
  -- Unprovable: `copyChecker.check` has no translated body (no `MethodUnfold` in `sync.Assumptions`;
  -- `copyChecker` is a `uintptr`, for which there is no `TypeRepr`). It is also false as
  -- stated: for the zero checker (what `is_Cond` provides), `check` does a successful
  -- `CompareAndSwapUintptr(c, 0, c)`, which needs (and changes) the full points-to of `c`.
  sorry -- Rocq: Admitted

theorem wp_runtime_notifyListAdd (l : loc) (l_v : notifyList.t) (dq : DFrac) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ typed_pointsto (GF := GF) l l_v dq }}
      (App (Val (@! runtime_notifyListAdd)) (Val #l))
    {{ (x : w32), RET #x; typed_pointsto (GF := GF) l l_v dq }} := by
  wp_start as Hl
  wp_apply wp_ArbitraryInt as %x _
  wp_end

theorem wp_runtime_notifyListNotifyOne (l : loc) (l_v : notifyList.t) (dq : DFrac) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ typed_pointsto (GF := GF) l l_v dq }}
      (App (Val (@! runtime_notifyListNotifyOne)) (Val #l))
    {{ RET #(); typed_pointsto (GF := GF) l l_v dq }} := by
  wp_start as Hl
  wp_end

theorem wp_runtime_notifyListNotifyAll (l : loc) (l_v : notifyList.t) (dq : DFrac) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ typed_pointsto (GF := GF) l l_v dq }}
      (App (Val (@! runtime_notifyListNotifyAll)) (Val #l))
    {{ RET #(); typed_pointsto (GF := GF) l l_v dq }} := by
  wp_start as Hl
  wp_end

theorem wp_runtime_notifyListWait (l : loc) (l_v : notifyList.t) (t : w32) (dq : DFrac) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ typed_pointsto (GF := GF) l l_v dq }}
      (App (App (Val (@! runtime_notifyListWait)) (Val #l)) (Val #t))
    {{ RET #(); typed_pointsto (GF := GF) l l_v dq }} := by
  wp_start as Hl
  wp_end

theorem wp_Cond__Signal (c : loc) (lk : interface.t_ok) :
    {{ is_Cond (GF := GF) c lk }}
      (App (Val (c @!! go.type.PointerType Cond @!! go!"Signal")) (Val #()))
    {{ RET #(); True }} := by
  wp_start as H
  simp only [is_Cond_unseal, is_Cond_def]
  iNamed H
  wp_auto
  wp_apply wp_copyChecker__check $$ [$Hchecker] with _
  wp_apply wp_runtime_notifyListNotifyOne $$ [$Hnotify] with _
  wp_end

theorem wp_Cond__Broadcast (c : loc) (lk : interface.t_ok) :
    {{ is_Cond (GF := GF) c lk }}
      (App (Val (c @!! go.type.PointerType Cond @!! go!"Broadcast")) (Val #()))
    {{ RET #(); True }} := by
  wp_start as H
  simp only [is_Cond_unseal, is_Cond_def]
  iNamed H
  wp_auto
  wp_apply wp_copyChecker__check $$ [$Hchecker] with _
  wp_apply wp_runtime_notifyListNotifyAll $$ [$Hnotify] with _
  wp_end

theorem wp_Cond__Wait (c : loc) (m : interface.t_ok) (R : IProp GF) :
    {{ is_Cond c m ∗ is_Locker m R ∗ R }}
      (App (Val (c @!! go.type.PointerType Cond @!! go!"Wait")) (Val #()))
    {{ RET #(); R }} := by
  wp_start as ⟨H, #Hlock, HR⟩
  simp only [is_Cond_unseal, is_Cond_def]
  iNamed H
  wp_auto
  wp_apply wp_copyChecker__check $$ [$Hchecker] with _
  wp_apply wp_runtime_notifyListAdd $$ [$Hnotify] with %x _
  unfold is_Locker
  iNamed Hlock
  wp_apply H_Unlock $$ HR
  wp_apply wp_runtime_notifyListWait $$ [$Hnotify] with _
  wp_apply H_Lock $$ [] with HR
  wp_end

end wps

end sync

end Perennial
end
