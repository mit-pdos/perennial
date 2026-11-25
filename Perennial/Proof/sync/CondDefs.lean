/-
Shared definitions of the proofs of `sync.Cond`: the copy checker's invariant
(`isCopyChecker`) and `isCond`.

Notes:
* `copyChecker`/`copyChecker.check` are trusted code (`TrustedCode/sync.lean`,
  `copyChecker` modeled as an `unsafe.Pointer`, i.e. `copyChecker.t = loc`)
  rather than axioms with no body, so `check` can be verified.
* `copyChecker.wp_check`: the spec
  `{{{ isPkgInit sync ∗ c ↦{dq} c_v }}} c.check() {{{ RET #(); c ↦{dq} c_v }}}`
  would be false: for the zero checker (the only one `isCond` provides), `check`
  does a successful `CompareAndSwapUintptr(c, 0, c)`, which needs full
  ownership and changes the value to `c`. The spec is instead
  `{{ isPkgInit sync ∗ isCopyChecker c }} c.check() {{ RET #(); True }}`,
  where `isCopyChecker c` is an invariant
  `c ↦ null ∨ c ↦□ c` (`copyCheckerInv`); `check` never panics under it.
* `isCond` contains `isCopyChecker c.[Cond.t, "checker"]` rather than
  `c.[Cond.t, "checker"] ↦□ zero_val copyChecker.t` (which `check` invalidates).
  `wp_NewCond` allocates the invariant.
-/
module

public import Perennial.Proof.sync.Base
public import Perennial.Spec.sync.atomic.LoadUint32
public import Perennial.Spec.sync.atomic.AddUint32
public import Perennial.Spec.sync.atomic.CompareAndSwapUint32

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace sync

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- The copy checker of a live `Cond` is either still `0`
(`null`) and fully owned by the invariant, or has been set (by the first
`check`) to its own address, after which it never changes. -/
abbrev copyCheckerInv (c : Loc) : IProp GF :=
  iprop(typedPointsto c (null : copyChecker) (DFrac.own 1) ∨
    typedPointsto c (c : copyChecker) DFrac.discard)

/-- See the module docstring. -/
def copyCheckerN : Namespace := nroot.@"copyChecker"

/-- See the module docstring. -/
def isCopyCheckerDef (c : Loc) : IProp GF := inv copyCheckerN (copyCheckerInv c)
@[irreducible] def isCopyChecker (c : Loc) : IProp GF := isCopyCheckerDef c
theorem isCopyChecker_unseal : @isCopyChecker = @isCopyCheckerDef := by
  funext; with_unfolding_all rfl

instance isCopyChecker_persistent (c : Loc) : Persistent (isCopyChecker (GF := GF) c) := by
  rw [isCopyChecker_unseal]; unfold isCopyCheckerDef; infer_instance

/-- The ticket counters of the `notifyList` at `l`, `wait` (the next ticket) and `notify` (the
next ticket to notify), which the Go model of the runtime's notify list
(`goose/model/overlay/sync/runtime.go`) reads and updates atomically. Its other fields are not
used. -/
abbrev notifyListInv (l : Loc) : IProp GF :=
  iprop(∃ (w n : w32), typedPointsto (structFieldRef notifyList go!"wait" l) w (DFrac.own 1) ∗
    typedPointsto (structFieldRef notifyList go!"notify" l) n (DFrac.own 1))

/-- See `isNotifyList`. -/
def notifyListN : Namespace := nroot.@"notifyList"

def isNotifyListDef (l : Loc) : IProp GF := inv notifyListN (notifyListInv l)
/-- `l` is a live `notifyList` (sealed): its ticket counters are in an invariant. -/
@[irreducible] def isNotifyList (l : Loc) : IProp GF := isNotifyListDef l
theorem isNotifyList_unseal : @isNotifyList = @isNotifyListDef := by
  funext; with_unfolding_all rfl

instance isNotifyList_persistent (l : Loc) : Persistent (isNotifyList (GF := GF) l) := by
  rw [isNotifyList_unseal]; unfold isNotifyListDef; infer_instance

/-- This means `c` is a condvar with underlying Locker `m`. -/
def isCondDef (c : Loc) (m : GoInterfaceOk) : IProp GF :=
  iprop("#Hi" ∷ isPkgInit (PROP := IProp GF) pkg_id.sync ∗
    "#Hc" ∷ typedPointsto (structFieldRef Cond go!"L" c) (interface.ok m) DFrac.discard ∗
    "#Hnotify" ∷ isNotifyList (structFieldRef Cond go!"notify" c) ∗
    -- not `c.[Cond.t, "checker"] ↦□ zero_val copyChecker.t`, which `check` breaks
    "#Hchecker" ∷ isCopyChecker (structFieldRef Cond go!"checker" c))
@[irreducible] def isCond (c : Loc) (m : GoInterfaceOk) : IProp GF := isCondDef c m
theorem isCond_unseal : @isCond = @isCondDef := by funext; with_unfolding_all rfl

instance isCond_persistent (c : Loc) (m : GoInterfaceOk) : Persistent (isCond (GF := GF) c m) := by
  rw [isCond_unseal]; unfold isCondDef named; infer_instance

end wps

/-! The atomic steps of the notify list's model on its invariant. -/
section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem wp_notifyList_load_wait
    (wp_LoadUint32 : sync.atomic.LoadUint32.spec (GF := GF) (hG := hG))
    (l : Loc) (Φ : val → IProp GF) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗ isNotifyList l -∗ (∀ w : w32, Φ #w) -∗
      WP (App (Val (@! sync.atomic.LoadUint32))
        (Val #(structFieldRef notifyList go!"wait" l))) {{ Φ }} := by
  iintro #Hpkg #Hl HΦ
  rw [isNotifyList_unseal]; unfold isNotifyListDef
  wp_apply_core wp_LoadUint32 $$ [] [-]
  · iexact Hpkg
  iinv Hl with Hi Hclose
  icases Hi with ⟨%w, %n, >Hw, >Hn⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists w
  iframe Hw
  iintro Hw
  imod Hmask with _
  imod Hclose $$ [Hw Hn] with _
  · inext; iexists w, n; iframe
  imodintro
  iapply HΦ

theorem wp_notifyList_load_notify
    (wp_LoadUint32 : sync.atomic.LoadUint32.spec (GF := GF) (hG := hG))
    (l : Loc) (Φ : val → IProp GF) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗ isNotifyList l -∗ (∀ n : w32, Φ #n) -∗
      WP (App (Val (@! sync.atomic.LoadUint32))
        (Val #(structFieldRef notifyList go!"notify" l))) {{ Φ }} := by
  iintro #Hpkg #Hl HΦ
  rw [isNotifyList_unseal]; unfold isNotifyListDef
  wp_apply_core wp_LoadUint32 $$ [] [-]
  · iexact Hpkg
  iinv Hl with Hi Hclose
  icases Hi with ⟨%w, %n, >Hw, >Hn⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists n
  iframe Hn
  iintro Hn
  imod Hmask with _
  imod Hclose $$ [Hw Hn] with _
  · inext; iexists w, n; iframe
  imodintro
  iapply HΦ

theorem wp_notifyList_add_wait
    (wp_AddUint32 : sync.atomic.AddUint32.spec (GF := GF) (hG := hG))
    (l : Loc) (v : w32) (Φ : val → IProp GF) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗ isNotifyList l -∗ (∀ w : w32, Φ #w) -∗
      WP (App (App (Val (@! sync.atomic.AddUint32))
        (Val #(structFieldRef notifyList go!"wait" l))) (Val #v)) {{ Φ }} := by
  iintro #Hpkg #Hl HΦ
  rw [isNotifyList_unseal]; unfold isNotifyListDef
  wp_apply_core wp_AddUint32 $$ [] [-]
  · iexact Hpkg
  iinv Hl with Hi Hclose
  icases Hi with ⟨%w, %n, >Hw, >Hn⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists w
  iframe Hw
  iintro Hw
  imod Hmask with _
  imod Hclose $$ [Hw Hn] with _
  · inext; iexists _, n; iframe
  imodintro
  iapply HΦ

theorem wp_notifyList_cas_notify
    (wp_CompareAndSwapUint32 : sync.atomic.CompareAndSwapUint32.spec (GF := GF) (hG := hG))
    (l : Loc) (old new : w32) (Φ : val → IProp GF) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗ isNotifyList l -∗ (∀ b : Bool, Φ #b) -∗
      WP (App (App (App (Val (@! sync.atomic.CompareAndSwapUint32))
        (Val #(structFieldRef notifyList go!"notify" l))) (Val #old)) (Val #new)) {{ Φ }} := by
  iintro #Hpkg #Hl HΦ
  rw [isNotifyList_unseal]; unfold isNotifyListDef
  wp_apply_core wp_CompareAndSwapUint32 $$ [] [-]
  · iexact Hpkg
  iinv Hl with Hi Hclose
  icases Hi with ⟨%w, %n, >Hw, >Hn⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists n, (DFrac.own 1)
  iframe Hn
  isplitr
  · ipureintro; split <;> rfl
  iintro Hn
  imod Hmask with _
  imod Hclose $$ [Hw Hn] with _
  · inext; iexists w, _; iframe
  imodintro
  iapply HΦ

end lemmas

end sync

end Perennial
