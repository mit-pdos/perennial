/-
Port of `new/proof/sync_proof/cond.v`: `sync.Cond`.

Lean deviations from Rocq:
* `copyChecker`/`copyChecker.check` are trusted code (`TrustedCode/sync.lean`,
  `copyChecker` modeled as an `unsafe.Pointer`, i.e. `copyChecker.t = loc`)
  instead of axioms with no body, so `check` can be verified.
* `copyChecker.wp_check`: Rocq (admitted)
  `{{{ isPkgInit sync ∗ c ↦{dq} c_v }}} c.check() {{{ RET #(); c ↦{dq} c_v }}}`
  is false: for the zero checker (the only one `isCond` provides), `check`
  does a successful `CompareAndSwapUintptr(c, 0, c)`, which needs full
  ownership and changes the value to `c`. New statement:
  `{{ isPkgInit sync ∗ isCopyChecker c }} c.check() {{ RET #(); True }}`,
  where the new `isCopyChecker c` is an invariant
  `c ↦ null ∨ c ↦□ c` (`copyCheckerInv`); `check` never panics under it.
* `isCond`: Rocq's conjunct `c.[Cond.t, "checker"] ↦□ zero_val copyChecker.t`
  (which `check` invalidates) becomes `isCopyChecker c.[Cond.t, "checker"]`.
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
abbrev copyCheckerInv (c : loc) : IProp GF :=
  iprop(typed_pointsto c (null : copyChecker.t) (DFrac.own 1) ∨
    typed_pointsto c (c : copyChecker.t) DFrac.discard)

/-- Lean addition (see the module docstring). -/
def copyCheckerN : Namespace := nroot.@"copyChecker"

/-- Lean addition (see the module docstring). -/
def isCopyCheckerDef (c : loc) : IProp GF := inv copyCheckerN (copyCheckerInv c)
@[irreducible] def isCopyChecker (c : loc) : IProp GF := isCopyCheckerDef c
theorem isCopyChecker_unseal : @isCopyChecker = @isCopyCheckerDef := by
  funext; with_unfolding_all rfl

instance isCopyChecker_persistent (c : loc) : Persistent (isCopyChecker (GF := GF) c) := by
  rw [isCopyChecker_unseal]; unfold isCopyCheckerDef; infer_instance

/-- This means `c` is a condvar with underlying Locker `m`. -/
def isCondDef (c : loc) (m : interface.t_ok) : IProp GF :=
  iprop("#Hi" ∷ isPkgInit (PROP := IProp GF) pkg_id.sync ∗
    "#Hc" ∷ typed_pointsto (struct_field_ref Cond.t go!"L" c) (interface.ok m) DFrac.discard ∗
    -- FIXME (Rocq): not accurate to assume it never changes, there should be an
    -- unknown notifyList struct in an invariant
    "#Hnotify" ∷ typed_pointsto (struct_field_ref Cond.t go!"notify" c)
      (zero_val notifyList.t) DFrac.discard ∗
    -- Lean: Rocq has `c.[Cond.t, "checker"] ↦□ zero_val copyChecker.t`, which `check` breaks.
    "#Hchecker" ∷ isCopyChecker (struct_field_ref Cond.t go!"checker" c))
@[irreducible] def isCond (c : loc) (m : interface.t_ok) : IProp GF := isCondDef c m
theorem isCond_unseal : @isCond = @isCondDef := by funext; with_unfolding_all rfl

instance isCond_persistent (c : loc) (m : interface.t_ok) : Persistent (isCond (GF := GF) c m) := by
  rw [isCond_unseal]; unfold isCondDef named; infer_instance

theorem wp_NewCond (m : interface.t_ok) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync }}
      (App (Val (@! NewCond)) (Val #(interface.ok m)))
    {{ (c : loc), RET #c; isCond c m }} := by
  wp_start as _
  wp_auto
  wp_pures
  wp_alloc c as Hc
  iStructNamed Hc
  ipersist L
  ipersist notify
  imod inv_alloc copyCheckerN ⊤ (copyCheckerInv _) $$ [checker] with #Hchecker
  · inext; ileft; iexact checker
  wp_pures
  iapply HΦ
  rw [isCond_unseal]; unfold isCondDef
  rw [isCopyChecker_unseal]; unfold isCopyCheckerDef
  iframe #
  done

/-- Lean deviation (Rocq, admitted:
`{{{ isPkgInit sync ∗ c ↦{dq} c_v }}} c.check() {{{ RET #(); c ↦{dq} c_v }}}`,
which is false for the zero checker: `check` CASes it to `c`). -/
theorem copyChecker.wp_check (c : loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isCopyChecker (GF := GF) c }}
      (App (Val (c @!! go.type.PointerType copyChecker @!! go!"check")) (Val #()))
    {{ RET #(); True }} := by
  wp_start as #Hinv
  rw [isCopyChecker_unseal]; unfold isCopyCheckerDef
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
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ typed_pointsto (GF := GF) l l_v dq }}
      (App (Val (@! runtime_notifyListAdd)) (Val #l))
    {{ (x : w32), RET #x; typed_pointsto (GF := GF) l l_v dq }} := by
  wp_start as Hl
  wp_apply wp_ArbitraryInt as %x _
  wp_end

theorem wp_runtime_notifyListNotifyOne (l : loc) (l_v : notifyList.t) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ typed_pointsto (GF := GF) l l_v dq }}
      (App (Val (@! runtime_notifyListNotifyOne)) (Val #l))
    {{ RET #(); typed_pointsto (GF := GF) l l_v dq }} := by
  wp_start as Hl
  wp_end

theorem wp_runtime_notifyListNotifyAll (l : loc) (l_v : notifyList.t) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ typed_pointsto (GF := GF) l l_v dq }}
      (App (Val (@! runtime_notifyListNotifyAll)) (Val #l))
    {{ RET #(); typed_pointsto (GF := GF) l l_v dq }} := by
  wp_start as Hl
  wp_end

theorem wp_runtime_notifyListWait (l : loc) (l_v : notifyList.t) (t : w32) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ typed_pointsto (GF := GF) l l_v dq }}
      (App (App (Val (@! runtime_notifyListWait)) (Val #l)) (Val #t))
    {{ RET #(); typed_pointsto (GF := GF) l l_v dq }} := by
  wp_start as Hl
  wp_end

theorem Cond.wp_Signal (c : loc) (lk : interface.t_ok) :
    {{ isCond (GF := GF) c lk }}
      (App (Val (c @!! go.type.PointerType Cond @!! go!"Signal")) (Val #()))
    {{ RET #(); True }} := by
  wp_start as H
  simp only [isCond_unseal, isCondDef]
  iNamed H
  wp_auto
  wp_apply copyChecker.wp_check $$ [$Hchecker]
  wp_apply wp_runtime_notifyListNotifyOne $$ [$Hnotify] with _
  wp_end

theorem Cond.wp_Broadcast (c : loc) (lk : interface.t_ok) :
    {{ isCond (GF := GF) c lk }}
      (App (Val (c @!! go.type.PointerType Cond @!! go!"Broadcast")) (Val #()))
    {{ RET #(); True }} := by
  wp_start as H
  simp only [isCond_unseal, isCondDef]
  iNamed H
  wp_auto
  wp_apply copyChecker.wp_check $$ [$Hchecker]
  wp_apply wp_runtime_notifyListNotifyAll $$ [$Hnotify] with _
  wp_end

theorem Cond.wp_Wait (c : loc) (m : interface.t_ok) (R : IProp GF) :
    {{ isCond c m ∗ isLocker m R ∗ R }}
      (App (Val (c @!! go.type.PointerType Cond @!! go!"Wait")) (Val #()))
    {{ RET #(); R }} := by
  wp_start as ⟨H, #Hlock, HR⟩
  simp only [isCond_unseal, isCondDef]
  iNamed H
  wp_auto
  wp_apply copyChecker.wp_check $$ [$Hchecker]
  wp_apply wp_runtime_notifyListAdd $$ [$Hnotify] with %x _
  unfold isLocker
  iNamed Hlock
  wp_apply H_Unlock $$ HR
  wp_apply wp_runtime_notifyListWait $$ [$Hnotify] with _
  wp_apply H_Lock $$ [] with HR
  wp_end

end wps

end sync

end Perennial
end
