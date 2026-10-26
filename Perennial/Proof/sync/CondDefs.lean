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

/-- This means `c` is a condvar with underlying Locker `m`. -/
def isCondDef (c : Loc) (m : GoInterfaceOk) : IProp GF :=
  iprop("#Hi" ∷ isPkgInit (PROP := IProp GF) pkg_id.sync ∗
    "#Hc" ∷ typedPointsto (structFieldRef Cond go!"L" c) (interface.ok m) DFrac.discard ∗
    -- FIXME: not accurate to assume it never changes, there should be an
    -- unknown notifyList struct in an invariant
    "#Hnotify" ∷ typedPointsto (structFieldRef Cond go!"notify" c)
      (zero_val notifyList) DFrac.discard ∗
    -- not `c.[Cond.t, "checker"] ↦□ zero_val copyChecker.t`, which `check` breaks
    "#Hchecker" ∷ isCopyChecker (structFieldRef Cond go!"checker" c))
@[irreducible] def isCond (c : Loc) (m : GoInterfaceOk) : IProp GF := isCondDef c m
theorem isCond_unseal : @isCond = @isCondDef := by funext; with_unfolding_all rfl

instance isCond_persistent (c : Loc) (m : GoInterfaceOk) : Persistent (isCond (GF := GF) c m) := by
  rw [isCond_unseal]; unfold isCondDef named; infer_instance

end wps

end sync

end Perennial
