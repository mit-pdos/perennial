/-
Shared definitions of the proofs of `sync`: its `isPkgInit`, the `rwmutex`/`WlockState`
states of the `RWMutex` protocol, the predicates `isMutex`/`ownMutex` of `sync.Mutex` (a
`lock`), and the `Locker` interface (`isLocker`, `isLockerWith`).

The rest of the shared definitions: the runtime semaphore (`SemaDefs`), `Cond` (`CondDefs`),
`Once` (`OnceDefs`), the low-level `RWMutex` protocol (`RWMutexDefs`, `sync.rwmutex.*`, meant
to be used qualified) and the guarded interface over it (`RWMutexGuard`), `WaitGroup`
(`WaitGroupDefs`) and its "join" idiom (`WaitGroupJoin`).
-/
module

public import Perennial.Code.sync
public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.sync
public import Perennial.Proof.sync.atomic.Base
public import Perennial.Proof.internal.race.Base
public import Perennial.Proof.internal.synctest.Base
public import Perennial.Proof.TokSet
public import Perennial.Algebra.AuthProp
public import Perennial.Golang.Theory.Lock

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

inductive rwmutex where
  | RLocked (num_readers : Nat)
  | Locked

inductive WlockState where
  | NotLocked (unnotified_readers : w32)
  | SignalingReaders (remaining_readers : w32)
  | WaitingForReaders
  | IsLocked

namespace sync

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.sync :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.sync :=
  build_get_is_pkg_init_wf

def isMutexDef (m : Loc) (R : IProp GF) : IProp GF := isLock m R
/-- This means `m` is a valid mutex with invariant `R` (sealed). -/
@[irreducible] def isMutex (m : Loc) (R : IProp GF) : IProp GF := isMutexDef m R
theorem isMutex_unseal : @isMutex = @isMutexDef := by funext; with_unfolding_all rfl

def ownMutexDef (m : Loc) : IProp GF := ownLock m
/-- This resource denotes ownership of the fact that the Mutex is currently
locked (sealed). -/
@[irreducible] def ownMutex (m : Loc) : IProp GF := ownMutexDef m
theorem ownMutex_unseal : @ownMutex = @ownMutexDef := by funext; with_unfolding_all rfl

theorem ownMutex_exclusive (m : Loc) : ⊢ ownMutex (GF := GF) m -∗ ownMutex m -∗ False := by
  simp only [ownMutex_unseal, ownMutexDef]
  exact ownLock_exclusive m

instance isMutex_ne (m : Loc) : NonExpansive (isMutex (GF := GF) m) := by
  rw [isMutex_unseal]; unfold isMutexDef; infer_instance

instance isMutex_persistent (m : Loc) (R : IProp GF) : Persistent (isMutex m R) := by
  rw [isMutex_unseal]; unfold isMutexDef; infer_instance

instance locked_timeless (m : Loc) : Timeless (ownMutex (GF := GF) m) := by
  rw [ownMutex_unseal]; unfold ownMutexDef; infer_instance

theorem init_Mutex (R : IProp GF) (E : CoPset) (m : Loc) :
    ⊢ typedPointsto (GF := GF) m (zero_val sync.Mutex) (DFrac.own 1) -∗ ▷ R ={E}=∗
      isMutex m R := by
  simp only [isMutex_unseal, isMutexDef]
  exact init_lock R E m

/-- `i` implements `Locker` with `Lock` producing `P` and `Unlock` consuming it. -/
def isLocker (i : GoInterfaceOk) (P : IProp GF) : IProp GF :=
  iprop("#H_Lock" ∷ iprop({{ True }} (App (Val #(methods i.ty go!"Lock" i.v)) (Val #()))
      {{ RET #(); P }}) ∗
    "#H_Unlock" ∷ iprop({{ P }} (App (Val #(methods i.ty go!"Unlock" i.v)) (Val #()))
      {{ RET #(); True }}))

instance isLocker_persistent (v : GoInterfaceOk) (P : IProp GF) :
    Persistent (isLocker v P) := by
  unfold isLocker named; infer_instance

/-- `i` implements `Locker` with `Lock` taking `Pre` and producing `P`, and `Unlock` taking
`P` and giving `Pre` back: a locker whose `Lock` needs a resource, such as
`rw.RLocker()`, whose `Lock` is `rw.RLock()` and needs one of the `RWMutex`'s bounded
reader tokens (`ownRWMutex`), which `Unlock` returns. `isLocker i P` is the case `Pre = True`
(`isLocker_isLockerWith`). -/
def isLockerWith (i : GoInterfaceOk) (Pre P : IProp GF) : IProp GF :=
  iprop("#H_Lock" ∷ iprop({{ Pre }} (App (Val #(methods i.ty go!"Lock" i.v)) (Val #()))
      {{ RET #(); P }}) ∗
    "#H_Unlock" ∷ iprop({{ P }} (App (Val #(methods i.ty go!"Unlock" i.v)) (Val #()))
      {{ RET #(); Pre }}))

instance isLockerWith_persistent (v : GoInterfaceOk) (Pre P : IProp GF) :
    Persistent (isLockerWith v Pre P) := by
  unfold isLockerWith named; infer_instance

theorem isLocker_isLockerWith (i : GoInterfaceOk) (P : IProp GF) :
    isLocker i P ⊢ isLockerWith i iprop(True) P := by
  unfold isLocker isLockerWith
  iintro ⟨#HL, #HU⟩
  isplitl
  · iexact HL
  · iexact HU

end wps

end sync

end Perennial
