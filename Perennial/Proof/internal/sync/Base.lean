/-
Shared definitions of the proofs of `internal/sync`: its `isPkgInit`, and the predicates of its
`Mutex`, `isLock m R` (the mutex at `m` protects `R`, persistent) and `ownLock m` (it is held).

`Mutex` is Go's `struct { state int32; sema uint32 }`, and its methods are the Go model
`goose/model/overlay/internal/sync`: a spin lock on `state` (`0` unlocked, `1` locked) over
`sync/atomic`'s compare-and-swap. The lock invariant owns `1/4` of `state ↦ v` and, when the lock
is free (`v = 0`), the other `3/4` and `R`; `ownLock m` is the `3/4` of `state ↦ 1`. (`sema` is
not used by the model.)
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.internal.sync
public import Perennial.Golang.Theory.Lock
public import Perennial.Spec.sync.atomic.CompareAndSwapInt32

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode OFE

namespace internal.sync

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.sync.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.sync :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.sync :=
  build_get_is_pkg_init_wf

end wps

end internal.sync

section lock
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.sync.Assumptions]

/-- The invariant of a `Mutex`'s `state` cell `s`. -/
abbrev lockInv (s : Loc) (R : IProp GF) : IProp GF :=
  iprop(∃ v : w32, s ↦{DFrac.own Qp.quarter} v ∗
      (if v = W32 0 then iprop(s ↦{DFrac.own Qp.threeQuarters} v ∗ R) else iprop(True)))

def isLockDef (m : Loc) (R : IProp GF) : IProp GF :=
  iprop("#Hinv" ∷ inv nroot (lockInv (structFieldRef internal.sync.Mutex go!"state" m) R))
/-- The `internal/sync.Mutex` at `m` is a lock protecting `R` (sealed). -/
@[irreducible] def isLock (m : Loc) (R : IProp GF) : IProp GF := isLockDef m R
theorem isLock_unseal : @isLock = @isLockDef := by funext; with_unfolding_all rfl

def ownLockDef (m : Loc) : IProp GF :=
  typedPointsto (GF := GF) (structFieldRef internal.sync.Mutex go!"state" m) (W32 1)
    (DFrac.own Qp.threeQuarters)
/-- The `internal/sync.Mutex` at `m` is locked, by the owner of this (sealed). -/
@[irreducible] def ownLock (m : Loc) : IProp GF := ownLockDef m
theorem ownLock_unseal : @ownLock = @ownLockDef := by funext; with_unfolding_all rfl

theorem ownLock_exclusive (m : Loc) : ⊢ ownLock (GF := GF) m -∗ ownLock m -∗ False := by
  rw [ownLock_unseal]; unfold ownLockDef
  iintro H1 H2
  icombine H1 H2 gives %Hv
  exfalso
  have : (3 / 4 + 3 / 4 : Rat) ≤ 1 := Hv.1
  grind

instance isLock_ne (m : Loc) : NonExpansive (isLock (GF := GF) m) where
  ne n R1 R2 h := by
    rw [isLock_unseal]; unfold isLockDef named
    refine (inv_ne nroot).ne ?_
    unfold lockInv
    refine exists_ne fun v => BI.sep_ne.ne .rfl ?_
    by_cases hv : v = W32 0
    · simp only [hv, ↓reduceIte]; exact BI.sep_ne.ne .rfl h
    · simp only [hv, ↓reduceIte]; exact .rfl

instance isLock_persistent (m : Loc) (R : IProp GF) : Persistent (isLock m R) := by
  rw [isLock_unseal]; unfold isLockDef named; infer_instance

instance locked_timeless (m : Loc) : Timeless (ownLock (GF := GF) m) := by
  rw [ownLock_unseal]; unfold ownLockDef; infer_instance

/-- A zero `Mutex` is an unlocked lock. -/
theorem init_lock (R : IProp GF) (E : CoPset) (m : Loc) :
    ⊢ typedPointsto (GF := GF) m (zero_val internal.sync.Mutex) (DFrac.own 1) -∗ ▷ R ={E}=∗
      isLock m R := by
  iintro Hm HR
  iStructNamed Hm
  rw [isLock_unseal]; unfold isLockDef
  icases (typedPointsto_quarter_three_quarter _ _).1 $$ state with ⟨Hl1, Hl2⟩
  imod inv_alloc nroot E (lockInv (structFieldRef internal.sync.Mutex go!"state" m) R)
    $$ [Hl1 Hl2 HR] with #Hinv
  · inext
    unfold lockInv
    iexists _
    simp only [zero_val_eq, ↓reduceIte]
    iframe
  imodintro
  iframe Hinv

/-- The model's acquiring step, `CompareAndSwapInt32(&m.state, 0, 1)` (`Lock`, `TryLock`): on
success the caller holds the lock and `R`. -/
theorem wp_lock_acquire
    (wp_CompareAndSwapInt32 : sync.atomic.CompareAndSwapInt32.spec (GF := GF) (hG := hG))
    (m : Loc) (R : IProp GF) (Φ : val → IProp GF) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗ isLock m R -∗
      (∀ b : Bool, (if b then ownLock m ∗ R else iprop(True)) -∗ Φ #b) -∗
      WP (App (App (App (Val (@! sync.atomic.CompareAndSwapInt32))
        (Val #(structFieldRef internal.sync.Mutex go!"state" m))) (Val #(W32 0))) (Val #(W32 1)))
        {{ Φ }} := by
  iintro #Hpkg #His HΦ
  rw [isLock_unseal]; unfold isLockDef
  iNamed His
  wp_apply_core wp_CompareAndSwapInt32 $$ [] [-]
  · iexact Hpkg
  iinv Hinv with Hi Hclose
  icases Hi with ⟨%v, >Hs, Hrest⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  by_cases hv : v = W32 0
  · subst hv
    simp only [↓reduceIte]
    icases Hrest with ⟨>Hs2, HR⟩
    ihave Hfull := (typedPointsto_quarter_three_quarter _ (W32 0)).2 $$ [Hs Hs2]
    · iframe
    inext
    iexists (W32 0), (DFrac.own 1)
    iframe Hfull
    isplitr
    · ipureintro; rfl
    iintro Hs
    icases (typedPointsto_quarter_three_quarter _ (W32 1)).1 $$ Hs with ⟨Hl1, Hl2⟩
    imod Hmask with _
    imod Hclose $$ [Hl1] with _
    · inext; iexists (W32 1); iframe
      simp only [show (W32 1 : w32) ≠ W32 0 by decide, ↓reduceIte]
      itrivial
    imodintro
    iapply HΦ
    simp only [decide_true, ↓reduceIte, ownLock_unseal, ownLockDef]
    iframe
  · inext
    iexists v, (DFrac.own Qp.quarter)
    iframe Hs
    isplitr
    · ipureintro; simp only [hv, ↓reduceIte]
    simp only [hv, ↓reduceIte]
    iintro Hs
    imod Hmask with _
    imod Hclose $$ [Hs Hrest] with _
    · inext; iexists v; iframe
    imodintro
    iapply HΦ
    simp only [hv, decide_false, Bool.false_eq_true, ↓reduceIte]
    itrivial

end lock

end Perennial
