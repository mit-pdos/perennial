/-
Port of `new/proof/sync_proof/cond.v`: `sync.Cond`.

Lean deviations from Rocq:
* `copyChecker`/`copyChecker.check` are trusted code (`TrustedCode/sync.lean`,
  `copyChecker` modeled as an `unsafe.Pointer`, i.e. `copyChecker.t = loc`)
  instead of axioms with no body, so `check` can be verified.
* `wp_copyChecker__check`: Rocq (admitted)
  `{{{ is_pkg_init sync ∗ c ↦{dq} c_v }}} c.check() {{{ RET #(); c ↦{dq} c_v }}}`
  is false: for the zero checker (the only one `is_Cond` provides), `check`
  does a successful `CompareAndSwapUintptr(c, 0, c)`, which needs full
  ownership and changes the value to `c`. New statement:
  `{{ is_pkg_init sync ∗ is_copyChecker c }} c.check() {{ RET #(); True }}`,
  where the new `is_copyChecker c` is an invariant
  `c ↦ null ∨ c ↦□ c` (`copyChecker_inv`); `check` never panics under it.
* `is_Cond`: Rocq's conjunct `c.[Cond.t, "checker"] ↦□ zero_val copyChecker.t`
  (which `check` invalidates) becomes `is_copyChecker c.[Cond.t, "checker"]`.
  `wp_NewCond` allocates the invariant.
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

/-- Lean addition: the copy checker of a live `Cond` is either still `0`
(`null`) and fully owned by the invariant, or has been set (by the first
`check`) to its own address, after which it never changes. -/
abbrev copyChecker_inv (c : loc) : IProp GF :=
  iprop(typed_pointsto c (null : copyChecker.t) (DFrac.own 1) ∨
    typed_pointsto c (c : copyChecker.t) DFrac.discard)

/-- Lean addition (see the module docstring). -/
def copyCheckerN : Namespace := nroot.@"copyChecker"

/-- Lean addition (see the module docstring). -/
def is_copyChecker_def (c : loc) : IProp GF := inv copyCheckerN (copyChecker_inv c)
@[irreducible] def is_copyChecker (c : loc) : IProp GF := is_copyChecker_def c
theorem is_copyChecker_unseal : @is_copyChecker = @is_copyChecker_def := by
  funext; with_unfolding_all rfl

instance is_copyChecker_persistent (c : loc) : Persistent (is_copyChecker (GF := GF) c) := by
  rw [is_copyChecker_unseal]; unfold is_copyChecker_def; infer_instance

/-- This means `c` is a condvar with underlying Locker `m`. -/
def is_Cond_def (c : loc) (m : interface.t_ok) : IProp GF :=
  iprop("#Hi" ∷ is_pkg_init (PROP := IProp GF) pkg_id.sync ∗
    "#Hc" ∷ typed_pointsto (struct_field_ref Cond.t go!"L" c) (interface.ok m) DFrac.discard ∗
    -- FIXME (Rocq): not accurate to assume it never changes, there should be an
    -- unknown notifyList struct in an invariant
    "#Hnotify" ∷ typed_pointsto (struct_field_ref Cond.t go!"notify" c)
      (zero_val notifyList.t) DFrac.discard ∗
    -- Lean: Rocq has `c.[Cond.t, "checker"] ↦□ zero_val copyChecker.t`, which `check` breaks.
    "#Hchecker" ∷ is_copyChecker (struct_field_ref Cond.t go!"checker" c))
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
  imod inv_alloc copyCheckerN ⊤ (copyChecker_inv _) $$ [checker] with #Hchecker
  · inext; ileft; iexact checker
  wp_pures
  iapply HΦ
  rw [is_Cond_unseal]; unfold is_Cond_def
  rw [is_copyChecker_unseal]; unfold is_copyChecker_def
  iframe #
  done

/-- Lean deviation (Rocq, admitted:
`{{{ is_pkg_init sync ∗ c ↦{dq} c_v }}} c.check() {{{ RET #(); c ↦{dq} c_v }}}`,
which is false for the zero checker: `check` CASes it to `c`). -/
theorem wp_copyChecker__check (c : loc) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ is_copyChecker (GF := GF) c }}
      (App (Val (c @!! go.type.PointerType copyChecker @!! go!"check")) (Val #()))
    {{ RET #(); True }} := by
  wp_start as #Hinv
  rw [is_copyChecker_unseal]; unfold is_copyChecker_def
  -- first `uintptr(*c) != uintptr(unsafe.Pointer(c))`
  wp_bind (Primitive1 _ _)
  iinv Hinv with >Hi
  icases Hi with (Hc | #Hc)
  · wp_apply_core wp_atomic_load _ _ c _ (null : loc) $$ Hc
    iintro Hc
    ihave %Hnn := typed_pointsto_not_null _ _ _ $$ Hc
    imodintro
    isplitl [Hc]
    · inext; ileft; iexact Hc
    wp_auto
    rw [decide_eq_false (Ne.symm Hnn)]
    wp_auto
    -- `CompareAndSwapUintptr(c, 0, c)`
    wp_bind (CmpXchg _ _ _)
    iinv Hinv with >Hi
    icases Hi with (Hc | #Hc)
    · wp_apply_core wp_cmpxchg_suc c (null : loc) null c _ _ rfl $$ Hc
      iintro Hc
      ipersist Hc
      imodintro
      isplitl []
      · inext; iright; iexact Hc
      wp_auto
      iapply HΦ
      itrivial
    · ihave %Hnn' := typed_pointsto_not_null _ _ _ $$ Hc
      wp_apply_core wp_cmpxchg_fail c c null c DFrac.discard _ _ Hnn $$ Hc
      iintro _
      imodintro
      isplitl []
      · inext; iright; iexact Hc
      wp_auto
      -- second `uintptr(*c) != uintptr(unsafe.Pointer(c))`
      wp_apply_core wp_atomic_load _ _ c _ c $$ Hc
      iintro _
      wp_auto
      iapply HΦ
      itrivial
  · wp_apply_core wp_atomic_load _ _ c _ c $$ Hc
    iintro _
    imodintro
    isplitl []
    · inext; iright; iexact Hc
    wp_auto
    iapply HΦ
    itrivial

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
  wp_apply wp_copyChecker__check $$ [$Hchecker]
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
  wp_apply wp_copyChecker__check $$ [$Hchecker]
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
  wp_apply wp_copyChecker__check $$ [$Hchecker]
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
