/-
Shared definitions of the proofs of the Go `context` package: its `isPkgInit` (`isInit`),
the ghost names and descriptor of a context (`ContextNames`, `ContextDesc`), the predicates
(`isContext`, `isContextDone`, `ContextClosed`, `isCancelCtxOf`, the `*cancelCtx` invariants,
`childCancelSpec`, `cancelSpec`, ...), the method-set facts of the initializer
(`errorString_is_error`, `deadlineExceededError_is_error`), and lemmas about them.

The design of the specs of Go's `context` package (the triples of its functions are in
`Perennial/Spec/context/`, one per function; the names below that are not the Link's are in
`Results.lean`).

Proved: `wp_Background`; `wp_WithCancel_Background` (`WithCancel(Background())`),
`wp_WithCancel` for a parent that is itself a `*cancelCtx` made by `WithCancel`
(`isCancelCtxCtx`), and `wp_WithCancel_any` for any parent (`isContext`; the new context's Done
proposition is then `True`); the `*cancelCtx` methods (`wp_cancelCtx_Done`, `wp_cancelCtx_Err`,
`wp_cancelCtx_Value`, `wp_cancelCtx_cancel`); `propagateCancel` (`wp_propagateCancel_background`,
`wp_propagateCancel_cancelCtx`, and `wp_propagateCancel_any` for any `isContext` parent and a
child whose `cancel` needs nothing of the parent); `wp_withCancel`, `wp_WithCancel_gen`,
`wp_removeChild`; `wp_parentCancelCtx` (any context), `wp_parentCancelCtx_background`,
`wp_parentCancelCtx_self`, `wp_parentCancelCtx_timer`; `wp_Cause`; the `*timerCtx` methods
(`wp_timerCtx_cancel`, `wp_timerCtx_Done`, ...) and `isContext_timerCtx`;
`wp_WithDeadlineCause`, and from it `wp_WithDeadline` and `wp_WithTimeout`.

Not proved: `propagateCancel`'s branches for a parent that `parentCancelCtx` does not resolve to a
`*cancelCtx` (a parent with an `AfterFunc` method, `parent.(afterFuncer)`, and the goroutine for
any other parent). They need the method set of the parent's dynamic type (for the type assertion
to `afterFuncer`, decided by `go_type_set` when it is known) and a spec of its `AfterFunc`. The
proofs show they are not taken: `Background()`'s `Done()` is `nil`, and every `isContext` is
resolved by `parentCancelCtx` (`"#HParentCC"`, true of the `*cancelCtx` and `*timerCtx` contexts
made here).

Design (see also the comments at each definition):
* Lazily determined Done channel. A context's Done channel cannot be fixed when the context
  is created: `cancelCtx.Done` makes the channel lazily at the first `Done()` call, or
  `cancel` stores the shared, already closed `closedchan` if it runs first. So a spec of
  `WithCancel` etc. that fixes the new context's channel at return time would be false.
  Instead:
  - `ContextDesc` has `Done_gn : ContextNames`, two ghost names: `doneGn`, a one-shot cell
    holding the Done channel once it is determined, and `closedGn`, the "context is done"
    flag.
  - `ContextClosed γ` (persistent): the context is done.
  - `isContextDone s ch γch` (persistent): `ch` is the Done channel; the done cell holds `ch`,
    and either `ch` is a broadcast channel with an existential proposition `Q` implying
    `□ s.PDone ∗ ContextClosed s.Done_gn`, or `ch` is closed (an invariant holds its state
    `Closed []`: `closedchan`) and the context is done. Client lemmas: `isContextDone_is_chan`,
    `isContextDone_receive` (`recvAu`, e.g. for a `select` case),
    `isContextDone_nonblocking_receive`, `isContextDone_agree` (successive `Done()` calls
    return the same channel), `isContextDone_weaken`.
  - `isContext`: `"#HDone"` returns some `ch` with `isContextDone s ch γch`; `"#HErr"` takes
    `ContextClosed s.Done_gn` for `cl = Done` (nothing otherwise) and returns
    `□ s.PDone ∗ ContextClosed s.Done_gn` for a non-nil error.
  - `isContext_weaken`: `isContext` is monotone in `PDone`.
  - `wp_WithCancel`, `wp_WithDeadlineCause`, `wp_WithDeadline`, `wp_WithTimeout` return
    fresh ghost names `γ' : ContextNames` for the new context (`Done_gn := γ'`).
* A `*cancelCtx` `c` with ghost names `γ` and Done proposition `P` (`isCancelCtxOf c γ P`,
  persistent):
  - `cancelCtxInv` (an invariant): the `atomic.Value` cells `done` and `err` (the trusted model
    of `sync/atomic.Value`, `sync.atomic.ownValue`), which the Go code also reads without the
    lock, with half of the ghost cells `γ.doneGn` / `γ.closedGn` while they are unset. Once the
    Done channel is set, `isContextDone` and `doneFresh` (it is not `closedchan`, or the context
    is done; a channel made by `Done()` is fresh by `chan.wp_make1_ne`); once `err` is set, it is
    a typed error (`isTypedErr`), `□ P` and `ContextClosed γ`.
  - `cancelCtxLockInv` (lock invariant of `c.mu`): `children`, `cause`, the other halves of the
    ghost cells, the right to close a Done channel made by `Done()`
    (`ownBroadcastChan .. .Pending`), and, until `c` is canceled, the children (`childrenInv`).
  - `childrenInv`: the `children` map (`map[canceler]struct{}`, keyed by interface values) with,
    for each key `k`, the stored spec `childCancelSpec P k` of `k.cancel(false, err, cause)`
    given `□ P`. The specs are stored in the lock invariant (impredicatively), so no induction
    over the depth of the context tree is needed: `wp_cancelCtx_cancel` uses the stored specs of
    `c`'s children, and `wp_propagateCancel_cancelCtx` stores `childCancelSpec_cancelCtx` for a
    new child.
  - `isCancelCtx c` (`∃ γ P, isCancelCtxOf c γ P`) is what `Value(&cancelCtxKey)` returns
    (`isCancelCtxAny`, in `isContext`'s `"#HValue"`); `isCancelCtxCtx ctx s` says that `ctx` is
    a `*cancelCtx` with the names and Done proposition of `s` (what `wp_WithCancel` needs of its
    parent).
* Cancel functions: `□ PDone' -∗ ▷ (ContextClosed γ' -∗ Φ #())` (`cancelSpec`): closing a
  broadcast channel needs the persistent `□ PDone`, and the call makes the context done.
  Propagation: a context made by `WithCancel(parent)` with a `*cancelCtx` parent is in the
  parent's `children` (or canceled at once if the parent is already done); the parent's `cancel`
  cancels each child before it returns (under the parent's lock). The child's Done proposition
  is `parent.PDone ∨ PDone'`.
* `isInit`: `"#Hclosedchan"`: the global `closedchan` holds a
  fixed channel; `"#HCanceled"`: the global `Canceled` holds a fixed typed error. Go never writes
  either after initialization. `parentCancelCtx` compares `parent.Done()` with `closedchan`.
* `isClosedchanInit` (persistent; ghost state): `closedchan`'s channel is closed (an
  invariant holds its state `Closed []`; `init` closes it), which `cancel` (it stores
  `closedchan`) and `Done` need. A conjunct of `isInit` (`isClosedchanInit_of_init`). Every `*cancelCtx`
  carries it (`isCancelCtxOf`); `wp_WithCancel_Background` (and `wp_withCancel`,
  `wp_WithCancel_gen`) take it as a premise; `wp_WithCancel` gets it from its parent.
* `isTypedErr e`: `e` is a non-nil error whose dynamic type is in `error`'s type set (so
  `e.(error)`, in `cancelCtx.Err`, succeeds). True of every Go error; tracked since the model has
  no method-set facts (`Canceled`'s and `DeadlineExceeded`'s are assumed in `isInit`).
* `isContext` includes `"#HValue"`, the spec of `c.Value(&cancelCtxKey)`: the result, if it
  is a `*cancelCtx`, is a valid one (`isCancelCtx`). `Cause`, `parentCancelCtx` (and through
  it `removeChild`) call `Value(&cancelCtxKey)` to find the innermost `*cancelCtx`.
* `wp_WithDeadlineCause`, `wp_WithDeadline`: the deadline is an existential `some d'` with
  `d' = d ∨ parent_desc.Deadline = some d'`, since when the parent's deadline is earlier,
  `WithDeadlineCause` returns `WithCancel(parent)`.
* `isContext` also says (`"#HErrDone"`, `"#HDoneFresh"`, `"#HParentCC"`, `"#HClosedchan"`) what a
  child's `propagateCancel` needs of its parent: once done, `Err()` returns a typed error; the
  Done channel is not `closedchan` unless the context is done; `parentCancelCtx` finds a
  `*cancelCtx` (so the branches above are not reached); and `context`'s `isClosedchanInit`.
* A `*cancelCtx`'s lock invariant has an extra resource `R` (`cancelCtxLockInv`,
  `isCancelCtxOfR`; `isCancelCtxOf` hides it): the fields of an enclosing struct that the same
  `mu` protects, a `*timerCtx`'s `timer` (`timerR`: `nil` or a timer from `AfterFunc`,
  `time.isFuncTimer`). `timerCtx.cancel` stops it (`time.Timer.wp_Stop_func`).
* A `*timerCtx` (the context of `WithDeadlineCause`) has Done proposition `True`: its cancel
  function, its `AfterFunc` callback and its parent's cancellation all cancel it with nothing
  to give. `time.AfterFunc` runs the callback in a goroutine (`time.wp_AfterFunc`; the runtime's
  timer is modeled in `TrustedCode/time.lean`).

Notes:
* Texan triples nested inside `isContext` are written out as
  `□ ∀ Φ, P -∗ ▷ (∀ x, Q -∗ Φ v) -∗ WP e {{ Φ }}`.
* The broadcast idiom fixes `hlc := HasLC.hasLC` and uses `[allG GF]`; the package-init
  instances are generic in `hlc`.
* A context whose Done channel is `nil` (never canceled, e.g. `Background()`) does not
  satisfy `isContext`: `isContextDone` includes `isChan`, which excludes `nil`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.context
public import Perennial.GeneratedProof.context
public import Perennial.Proof.sync.atomic.Base
public import Perennial.Proof.sync.Base
public import Perennial.Proof.time.Base
public import Perennial.Proof.errors.Base
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace context

/-- Ghost names of a context (see the file header). -/
structure ContextNames where
  mk ::
  /-- `dghostVar (Option GoChan)`: the context's Done channel, fixed (as `some ch`, then
  discarded) by whoever determines it, e.g. the first `Done()` or `cancel` of a `*cancelCtx`. -/
  doneGn : GName
  /-- `dghostVar Bool`: `true` (discarded) once the context is done. -/
  closedGn : GName

/-! Context logical descriptor. -/
/-- The Done channel is not part of the descriptor: `Done_gn : ContextNames` holds the ghost
names through which the Done channel is determined later (see the file header). -/
structure ContextDesc [GooseExts] (PROP : Type) where
  mk ::
  Values : GMap GoInterface GoInterface
  Deadline : Option time.Time
  Done_gn : ContextNames
  PDone : PROP

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- Namespace of the invariant saying that `closedchan` is closed. -/
def closedchanN : Namespace := nroot .@ "context.closedchan"

/-- `e` is a non-nil error whose dynamic type is in the type set of `error` (so the type
assertion `e.(error)` succeeds). Every error value has this property in Go; in the model it is a
fact about the error's dynamic type (`go_type_set` proves it from the type's method set), so it
is tracked explicitly. -/
def isTypedErr [GoSemanticsFunctions] (e : GoInterface) : Prop :=
  match e with
  | .ok ii => go.typeSetContains ii.ty go.error = true
  | .nil => False

theorem isTypedErr_ne_nil [GoSemanticsFunctions] {e : GoInterface} (h : isTypedErr e) : e ≠ interface.nil := by
  cases e <;> simp_all [isTypedErr]

/-- `context`'s package-init fact about `closedchan`: the global `closedchan` holds a fixed
channel, which is closed (`init` closes it; Go never writes `closedchan` afterwards): an
invariant holds its channel state `Closed []`. Persistent. Part of `isInit` (`"#Hcci"`;
`isClosedchanInit_of_init`), so any program that has initialized `context` has it. Every
`*cancelCtx` also carries it (`isCancelCtxOf`'s `"#Hcci"`), so only creating one from scratch
(`wp_withCancel`, `wp_WithCancel_gen`, `wp_WithCancel_Background`) takes it as a premise. -/
def isClosedchanInit : IProp GF :=
  iprop(∃ (ch : GoChan) (γ : ChanNames), globalAddr context.closedchan ↦□ ch ∗
    isChan ch γ Unit ∗ inv closedchanN (ownChan γ Unit (.Closed [])))

instance isClosedchanInit_pers : Persistent (isClosedchanInit (GF := GF)) := by
  unfold isClosedchanInit; infer_instance

/-- The package invariant:
* `"Hgoroutines"`: the `goroutines` counter;
* `"#Hclosedchan"`: the global `closedchan` holds a fixed channel;
* `"#HCanceled"`: the global `Canceled` holds a fixed error (`errors.New("context
  canceled")`), whose type implements `error` (`isTypedErr`);
* `"#HDeadlineExceeded"`: likewise for `DeadlineExceeded` (`deadlineExceededError{}`);
* `"#Hcci"`: `closedchan`'s channel is closed (`isClosedchanInit`, ghost state: the channel's
  names and an invariant on its state). Appended last, so patterns ending in a catch-all
  that destructure the earlier conjuncts are unaffected.
Go never writes `closedchan`, `Canceled` or `DeadlineExceeded` after initialization. -/
abbrev isInit : IProp GF :=
  iprop("Hgoroutines" ∷
    inv nroot (∃ g, sync.atomic.ownInt32 (globalAddr context.goroutines) (DFrac.own 1) g) ∗
  "#Hclosedchan" ∷ (∃ ch : GoChan, globalAddr context.closedchan ↦□ ch) ∗
  "#HCanceled" ∷ (∃ e : GoInterface, globalAddr context.Canceled ↦□ e ∗ ⌜isTypedErr e⌝) ∗
  "#HDeadlineExceeded" ∷
    (∃ e : GoInterface, globalAddr context.DeadlineExceeded ↦□ e ∗ ⌜isTypedErr e⌝) ∗
  "#Hcci" ∷ isClosedchanInit ∗
  "_" ∷ True)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.context :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.context :=
  build_get_is_pkg_init_wf

end init

section is_error
variable [GooseExts] [GoLocalContext] [GoGlobalContext] [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- `*errors.errorString` is in the type set of `error` (it has the method `Error() string`,
with a pointer receiver): from the method sets of `errors.Assumptions`. -/
theorem errorString_is_error :
    go.typeSetContains (go.GoType.PointerType errors.errorString.ty) go.error = true := by
  go_type_set

/-- `context.deadlineExceededError` is in the type set of `error` (it has the method
`Error() string`, with a value receiver). -/
theorem deadlineExceededError_is_error :
    go.typeSetContains context.deadlineExceededError.ty go.error = true := by
  go_type_set

end is_error

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

open ContextDesc

theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.context ⊢ isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.context

/-- `closedchan` is closed once `context` is initialized. -/
theorem isClosedchanInit_of_init :
    isPkgInit (PROP := IProp GF) pkg_id.context ⊢ isClosedchanInit (GF := GF) := by
  iintro #Hpkg
  ihave #Hi := isInit_access $$ Hpkg
  icases Hi with ⟨-, -, -, -, #Hcci, -⟩
  iexact Hcci

/-- `&cancelCtxKey` converted to `any`: the key for which `Value` returns the
innermost enclosing `*cancelCtx`. -/
abbrev cancelCtxKeyAny [GoSemanticsFunctions] : GoInterface :=
  interface.mkOk (go.GoType.PointerType go.int) #(globalAddr context.cancelCtxKey)

/-- The context with ghost names `γ` is done (canceled or past its deadline). Persistent. -/
def ContextClosed (γ : ContextNames) : IProp GF :=
  dghostVar γ.closedGn .discard true

instance contextClosed_pers (γ : ContextNames) : Persistent (ContextClosed (GF := GF) γ) := by
  unfold ContextClosed; infer_instance

/-- `ch` (with channel names `γch`) is the Done channel of the context `s`: the context's
done cell holds `ch`, and either
* `ch` is a broadcast channel whose closing implies that `s` is done (`ContextClosed`) and
  `□ s.PDone` (the broadcast proposition `Q` is existential: a `*cancelCtx` whose channel is
  made by `Done()` uses `Q := s.PDone ∗ ContextClosed s.Done_gn`); or
* `ch` is closed (its state `Closed []` is in an invariant), and `s` is done: a `*cancelCtx`
  whose `cancel` runs before any `Done()` stores the shared, already closed `closedchan`.
Persistent. -/
def isContextDoneDef (s : ContextDesc (IProp GF)) (ch : GoChan) (γch : ChanNames) :
    IProp GF :=
  iprop(dghostVar s.Done_gn.doneGn .discard (some ch) ∗
    ((∃ Q : IProp GF, ownBroadcastChan ch γch Q .Unknown ∗
        □ (□ Q -∗ □ s.PDone ∗ ContextClosed s.Done_gn)) ∨
     (isChan ch γch Unit ∗ inv closedchanN (ownChan γch Unit (.Closed [])) ∗
        □ s.PDone ∗ ContextClosed s.Done_gn)))

@[irreducible] def isContextDone (s : ContextDesc (IProp GF)) (ch : GoChan)
    (γch : ChanNames) : IProp GF := isContextDoneDef s ch γch

theorem isContextDone_unseal : @isContextDone = @isContextDoneDef := by
  funext; with_unfolding_all rfl

instance isContextDone_pers (s : ContextDesc (IProp GF)) (ch : GoChan) (γch : ChanNames) :
    Persistent (isContextDone s ch γch) := by
  rw [isContextDone_unseal]; unfold isContextDoneDef; infer_instance

/-- `isContextDone` only depends on the descriptor's `Done_gn` and `PDone`. -/
theorem isContextDone_congr (s s' : ContextDesc (IProp GF)) (ch : GoChan) (γch : ChanNames)
    (h1 : s.Done_gn = s'.Done_gn) (h2 : s.PDone = s'.PDone) :
    isContextDone s ch γch ⊢ isContextDone s' ch γch := by
  rw [isContextDone_unseal]; unfold isContextDoneDef; rw [h1, h2]

/-! The internal state of a `*cancelCtx`. -/

/-- Namespace of the `*cancelCtx` invariants (`cancelCtxInv`). -/
def cancelCtxN : Namespace := nroot .@ "context.cancelCtx"

/-- The content of the `done` cell (`atomic.Value`): `nil` until the Done channel is
determined, then the channel as an `any`. -/
def doneAny (od : Option GoChan) : GoInterface :=
  match od with
  | none => interface.nil
  | some ch => interface.mkOk (go.GoType.ChannelType go.ChanDir.sendrecv (go.GoType.StructType []))
      #ch

/-- A descriptor with ghost names `γ` and Done proposition `P` (for `isContextDone`, which only
reads these two). -/
abbrev cdesc (γ : ContextNames) (P : IProp GF) : ContextDesc (IProp GF) :=
  ⟨∅, none, γ, P⟩

/-- The Done channel `ch` of a `*cancelCtx` is not the shared `closedchan`, or the context is
done (`cancel` stores `closedchan` only once it is canceled). Persistent. -/
def doneFresh (γ : ContextNames) (P : IProp GF) (ch : GoChan) : IProp GF :=
  iprop((∃ cch : GoChan, globalAddr context.closedchan ↦□ cch ∗ ⌜ch ≠ cch⌝) ∨
    (□ P ∗ ContextClosed γ))

instance doneFresh_pers (γ : ContextNames) (P : IProp GF) (ch : GoChan) :
    Persistent (doneFresh γ P ch) := by
  unfold doneFresh; infer_instance

/-- The timeless part of `doneFresh`: the Done channel `ch` is not `closedchan`, or the context
is done. Persistent. -/
def doneFreshT (γ : ContextNames) (ch : GoChan) : IProp GF :=
  iprop((∃ cch : GoChan, globalAddr context.closedchan ↦□ cch ∗ ⌜ch ≠ cch⌝) ∨ ContextClosed γ)

instance doneFreshT_pers (γ : ContextNames) (ch : GoChan) :
    Persistent (doneFreshT (GF := GF) γ ch) := by
  unfold doneFreshT; infer_instance

instance doneFreshT_timeless (γ : ContextNames) (ch : GoChan) :
    Timeless (doneFreshT (GF := GF) γ ch) := by
  unfold doneFreshT ContextClosed; infer_instance

/-- The invariant of a `*cancelCtx` `c` with names `γ` and Done proposition `P`: the
`atomic.Value` cells `done` and `err`, which the Go code also reads without `c.mu`.
* `done` holds `doneAny od`; while `od = none`, half of the done cell `γ.doneGn` (the other
  half is in the lock invariant); once `od = some ch`, `isContextDone` for `ch` and
  `doneFresh` (`ch` is not `closedchan`, or the context is done).
* `err` holds `e`; while `e = nil`, half of the closed flag `γ.closedGn` (the other half is
  in the lock invariant); once set, `e` is a typed error, `□ P` and `ContextClosed γ`. -/
def cancelCtxInv (c : Loc) (γ : ContextNames) (P : IProp GF) : IProp GF :=
  iprop(∃ (od : Option GoChan) (e : GoInterface),
    "Hdone" ∷ sync.atomic.ownValue (structFieldRef context.cancelCtx go!"done" c) (DFrac.own 1)
      (doneAny od) ∗
    "Hdg" ∷ (match od with
      | none => dghostVar γ.doneGn (.own (1 : Qp).half) (none : Option GoChan)
      | some ch => ∃ γch, isContextDone (cdesc γ P) ch γch ∗ doneFresh γ P ch) ∗
    "Herr" ∷ sync.atomic.ownValue (structFieldRef context.cancelCtx go!"err" c) (DFrac.own 1) e ∗
    "Hcg" ∷ (if e = interface.nil then dghostVar γ.closedGn (.own (1 : Qp).half) false
      else iprop(⌜isTypedErr e⌝ ∗ □ P ∗ ContextClosed γ)))

/-- The spec a parent `*cancelCtx` (with Done proposition `P`) keeps for each child `k` in its
`children` map: `k.cancel(false, err, cause)` for a typed error `err`, given `□ P`. -/
def childCancelSpec (P : IProp GF) (k : GoInterface) : IProp GF :=
  match k with
  | .ok ki => iprop(□ (∀ (err cause : GoInterface) (Φ : val → IProp GF),
      ⌜isTypedErr err⌝ -∗ □ P -∗ ▷ Φ #() -∗
      WP (App (App (App (Val #(methods ki.ty go!"cancel" ki.v)) (Val #false)) (Val #err))
        (Val #cause)) {{ Φ }}))
  | .nil => iprop(False)

instance childCancelSpec_pers (P : IProp GF) (k : GoInterface) :
    Persistent (childCancelSpec P k) := by
  unfold childCancelSpec; split <;> infer_instance

/-- The `children` map of a `*cancelCtx` that is not canceled: `nil`, or a map whose keys all
satisfy `childCancelSpec`. -/
def childrenInv (m : GoMap) (P : IProp GF) : IProp GF :=
  iprop(⌜m = map.nil⌝ ∨ ∃ M : GMap GoInterface Unit, ownMap m (DFrac.own 1) M ∗
    □ (∀ (k : GoInterface) (u : Unit), ⌜M !! k = some u⌝ -∗ childCancelSpec P k))

/-- Lock invariant of `c.mu` for a `*cancelCtx` `c`: the fields only accessed with `c.mu` held
(`children`, `cause`), and the other halves of the ghost cells of `cancelCtxInv`: `closed` is
whether `c` is canceled; until then, the children (`childrenInv`) and, once the Done channel
`ch` is made (by `Done()`), the right to close it (`ownBroadcastChan .. .Pending`). A canceled
`c` has a Done channel (`cancel` stores `closedchan` if there is none). `R`: the fields of an
enclosing struct that `c.mu` also protects (a `*timerCtx`'s `timer`; `True` for a plain
`*cancelCtx`). -/
def cancelCtxLockInv (c : Loc) (γ : ContextNames) (P R : IProp GF) : IProp GF :=
  iprop(∃ (children : GoMap) (cause : GoError) (od : Option GoChan) (closed : Bool),
    "children" ∷ structFieldRef context.cancelCtx go!"children" c ↦ children ∗
    "cause" ∷ structFieldRef context.cancelCtx go!"cause" c ↦ cause ∗
    "Hcl" ∷ (if closed then iprop(ContextClosed γ ∗ ⌜children = map.nil⌝)
      else iprop(dghostVar γ.closedGn (.own (1 : Qp).half) false ∗ childrenInv children P)) ∗
    "Hod" ∷ (match od with
      | none => iprop(dghostVar γ.doneGn (.own (1 : Qp).half) (none : Option GoChan) ∗
          ⌜closed = false⌝)
      | some ch => iprop(dghostVar γ.doneGn .discard (some ch) ∗
          (if closed then iprop(True)
           else ∃ γch, ownBroadcastChan ch γch iprop(P ∗ ContextClosed γ) .Pending))) ∗
    "HR" ∷ R)

/-- `c` is a (shared) `*cancelCtx` with ghost names `γ`, Done proposition `P` and extra lock
resource `R` (`cancelCtxLockInv`); it carries `context`'s `isClosedchanInit` (`"#Hcci"`), which
its methods need. -/
def isCancelCtxOfR (c : Loc) (γ : ContextNames) (P R : IProp GF) : IProp GF :=
  iprop("#Hmu" ∷ sync.isMutex (structFieldRef context.cancelCtx go!"mu" c)
      (cancelCtxLockInv c γ P R) ∗
    "#Hinv" ∷ inv cancelCtxN (cancelCtxInv c γ P) ∗
    "#Hcci" ∷ isClosedchanInit)

instance isCancelCtxOfR_pers (c : Loc) (γ : ContextNames) (P R : IProp GF) :
    Persistent (isCancelCtxOfR c γ P R) := by
  unfold isCancelCtxOfR; infer_instance

/-- `c` is a (shared) `*cancelCtx` with ghost names `γ` and Done proposition `P` (for some
extra lock resource, `isCancelCtxOfR`). -/
def isCancelCtxOf (c : Loc) (γ : ContextNames) (P : IProp GF) : IProp GF :=
  iprop(∃ R : IProp GF,
    "#Hmu" ∷ sync.isMutex (structFieldRef context.cancelCtx go!"mu" c)
      (cancelCtxLockInv c γ P R) ∗
    "#Hinv" ∷ inv cancelCtxN (cancelCtxInv c γ P) ∗
    "#Hcci" ∷ isClosedchanInit)

instance isCancelCtxOf_pers (c : Loc) (γ : ContextNames) (P : IProp GF) :
    Persistent (isCancelCtxOf c γ P) := by
  unfold isCancelCtxOf; infer_instance

theorem isCancelCtxOfR_of (c : Loc) (γ : ContextNames) (P R : IProp GF) :
    isCancelCtxOfR c γ P R ⊢ isCancelCtxOf c γ P := by
  unfold isCancelCtxOfR isCancelCtxOf
  iintro H
  iexists R
  iexact H

theorem isCancelCtxOf_closedchan (c : Loc) (γ : ContextNames) (P : IProp GF) :
    isCancelCtxOf c γ P ⊢ isClosedchanInit := by
  iintro #Hc
  iunfold isCancelCtxOf at Hc
  icases Hc with ⟨%R, -, -, #Hcci⟩
  iexact Hcci

/-- `c` is a (shared) `*cancelCtx`. -/
def isCancelCtx (c : Loc) : IProp GF :=
  iprop(∃ (γ : ContextNames) (P : IProp GF), isCancelCtxOf c γ P)

instance isCancelCtx_pers (c : Loc) : Persistent (isCancelCtx (GF := GF) c) := by
  unfold isCancelCtx; infer_instance

/-- The context `ctx` (described by `s`) is a `*cancelCtx` made by `WithCancel`, with the ghost
names and Done proposition of `s`: what `wp_WithCancel` needs of its parent. Persistent. -/
def isCancelCtxCtx (ctx : GoInterfaceOk) (s : ContextDesc (IProp GF)) : IProp GF :=
  iprop(∃ p : Loc, ⌜ctx = interface.mk (go.GoType.PointerType context.cancelCtx.ty) #p⌝ ∗
    isCancelCtxOf p s.Done_gn s.PDone)

instance isCancelCtxCtx_pers (ctx : GoInterfaceOk) (s : ContextDesc (IProp GF)) :
    Persistent (isCancelCtxCtx (GF := GF) ctx s) := by
  unfold isCancelCtxCtx; infer_instance

/-- The result of `Value(&cancelCtxKey)`: if it is a `*cancelCtx`, then it is a
valid one. -/
def isCancelCtxAny (v : GoInterface) : IProp GF :=
  match v with
  | interface.ok ii =>
    if ii.ty = go.GoType.PointerType context.cancelCtx.ty then
      iprop(∃ c : Loc, ⌜ii.v = #c⌝ ∗ isCancelCtx c)
    else iprop(True)
  | interface.nil => iprop(True)

instance isCancelCtxAny_pers (v : GoInterface) : Persistent (isCancelCtxAny (GF := GF) v) := by
  unfold isCancelCtxAny
  split
  · split <;> infer_instance
  · infer_instance

def isContextDef (c : GoInterfaceOk) (s : ContextDesc (IProp GF)) : IProp GF :=
  iprop(
  "#HDeadline" ∷
    □ (∀ Φ : val → IProp GF, True -∗
      ▷ (True -∗ Φ (PairV #(s.Deadline.getD (zero_val time.Time))
                          #(match s.Deadline with | none => false | some _ => true))) -∗
      WP (App (Val #(methods c.ty go!"Deadline" c.v)) (Val #())) {{ Φ }}) ∗
  "#HDone" ∷
    □ (∀ Φ : val → IProp GF, True -∗
      ▷ (∀ (ch : GoChan) (γch : ChanNames), isContextDone s ch γch -∗ Φ #ch) -∗
      WP (App (Val #(methods c.ty go!"Done" c.v)) (Val #())) {{ Φ }}) ∗
  "#HErr" ∷
    (∀ cl : Broadcast, □ (∀ Φ : val → IProp GF,
      (match cl with
       | .Done => ContextClosed s.Done_gn
       | _ => iprop(True)) -∗
      ▷ (∀ err : GoInterface,
          (match cl with
           | .Done => iprop(⌜err ≠ interface.nil⌝)
           | _ => if err = interface.nil then iprop(True)
                  else iprop(□ s.PDone ∗ ContextClosed s.Done_gn)) -∗
          Φ #err) -∗
      WP (App (Val #(methods c.ty go!"Err" c.v)) (Val #())) {{ Φ }})) ∗
  "#HValue" ∷
    □ (∀ Φ : val → IProp GF, True -∗
      ▷ (∀ v : GoInterface, isCancelCtxAny v -∗ Φ #v) -∗
      WP (App (Val #(methods c.ty go!"Value" c.v)) (Val #cancelCtxKeyAny)) {{ Φ }}) ∗
  "#HErrDone" ∷
    □ (∀ Φ : val → IProp GF, ContextClosed s.Done_gn -∗
      ▷ (∀ err : GoInterface, ⌜isTypedErr err⌝ -∗ Φ #err) -∗
      WP (App (Val #(methods c.ty go!"Err" c.v)) (Val #())) {{ Φ }}) ∗
  "#HDoneFresh" ∷
    □ (∀ ch : GoChan, dghostVar s.Done_gn.doneGn .discard (some ch) ={⊤}=∗
      doneFreshT s.Done_gn ch) ∗
  "#HParentCC" ∷ (⌜c.ty ≠ context.stopCtx.ty⌝ ∗
    □ (∀ (ch cch : GoChan) (Φ : val → IProp GF),
      dghostVar s.Done_gn.doneGn .discard (some ch) -∗
      globalAddr context.closedchan ↦□ cch -∗ ⌜ch ≠ cch⌝ -∗
      ▷ (∀ p : Loc, isCancelCtx p -∗ Φ (PairV #p #true)) -∗
      WP (App (Val (@! context.parentCancelCtx)) (Val #(interface.ok c))) {{ Φ }})) ∗
  "#HClosedchan" ∷ isClosedchanInit)

/-- `c` is a valid context described by `s` (not sealed). See the file header:
* `"#HDone"` returns some channel `ch` with `isContextDone s ch γch`, which carries the
  broadcast-channel knowledge about the Done channel.
* `"#HErr"` takes `ContextClosed s.Done_gn` (precondition, only for `cl = Done`) and gives
  `□ s.PDone ∗ ContextClosed s.Done_gn` (postcondition, for a non-nil error).
* `"#HValue"` only specifies the key `&cancelCtxKey`; the `Values` field of `ContextDesc` is
  unused.
* `"#HErrDone"`: once the context is done, `Err()` returns a typed error (`isTypedErr`), which
  a child's `cancel` stores (and its `Err()` type-asserts to `error`).
* `"#HDoneFresh"`: the Done channel `ch` (once known) is not `closedchan`, or the context is
  done.
* `"#HParentCC"`: `c` is not a `stopCtx`, and `parentCancelCtx(c)` finds a `*cancelCtx` once the
  Done channel `ch` is known (and is not `closedchan`). So `propagateCancel(c, child)` registers
  `child` with that `*cancelCtx`, or cancels it at once, and never reaches its branches for
  other parents (an `afterFuncer`, whose type assertion the model cannot decide, or the
  goroutine), nor does `removeChild(c, child)` reach its `stopCtx` branch. True of the contexts
  this file makes (`*cancelCtx`, `*timerCtx`).
* `"#HClosedchan"`: `context`'s `isClosedchanInit`. -/
abbrev isContext (c : GoInterfaceOk) (s : ContextDesc (IProp GF)) : IProp GF :=
  isContextDef c s

instance isContext_pers (c : GoInterfaceOk) (s : ContextDesc (IProp GF)) :
    Persistent (isContext c s) := by
  unfold isContext isContextDef; infer_instance

/-! Client lemmas for the Done channel (clients use them instead of `ownBroadcastChan`
lemmas). -/

theorem isContextDone_is_chan (s : ContextDesc (IProp GF)) (ch : GoChan) (γch : ChanNames) :
    isContextDone s ch γch ⊢ isChan ch γch Unit := by
  rw [isContextDone_unseal]; unfold isContextDoneDef
  iintro ⟨-, (⟨%Q, #Hbc, -⟩ | ⟨#Hch, -⟩)⟩
  · iapply ownBroadcastChan_is_chan $$ Hbc
  · iexact Hch

/-- Successive `Done()` calls return the same channel. -/
theorem isContextDone_agree (s : ContextDesc (IProp GF)) (ch1 ch2 : GoChan)
    (γ1 γ2 : ChanNames) :
    isContextDone s ch1 γ1 ∗ isContextDone s ch2 γ2 ⊢ ⌜ch1 = ch2⌝ := by
  rw [isContextDone_unseal]; unfold isContextDoneDef
  iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
  ihave %h := dghostVar_agree _ _ _ _ _ $$ H1 H2
  ipureintro; exact Option.some.inj h

/-- A receive from a channel whose state `Closed []` is in an invariant returns at once. -/
theorem closed_chan_receive (γ : ChanNames) (Φ : Unit → Bool → IProp GF) :
    ⊢ inv closedchanN (ownChan γ Unit (.Closed [])) -∗ Φ () false -∗ recvAu γ Unit Φ := by
  iintro #Hinv HΦ
  unfold recvAu
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists .Closed []
  iframe Hi
  dsimp only
  iintro Hch
  imod Hmask with -
  imod Hclose $$ Hch with -
  imodintro
  iexact HΦ

/-- A nonblocking receive from a channel whose state `Closed []` is in an invariant is ready. -/
theorem closed_chan_nonblocking_receive (γ : ChanNames) (Φ : Unit → Bool → IProp GF)
    (Φnotready : IProp GF) :
    ⊢ inv closedchanN (ownChan γ Unit (.Closed [])) -∗ Φ () false -∗
      nonblockingRecvAuAlt γ Unit Φ Φnotready := by
  iintro #Hinv HΦ
  unfold nonblockingRecvAuAlt
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists .Closed []
  iframe Hi
  dsimp only
  iintro Hch
  imod Hmask with -
  imod Hclose $$ Hch with -
  imodintro
  iexact HΦ

/-- Receiving from the Done channel (e.g. as a `select` case) returns only once the context is
done. -/
theorem isContextDone_receive (s : ContextDesc (IProp GF)) (ch : GoChan) (γch : ChanNames)
    (Φ : Unit → Bool → IProp GF) :
    ⊢ isContextDone s ch γch -∗
      (□ s.PDone ∗ ContextClosed s.Done_gn -∗ Φ () false) -∗
      recvAu γch Unit Φ := by
  rw [isContextDone_unseal]; unfold isContextDoneDef
  iintro ⟨-, (⟨%Q, #Hbc, #HQ⟩ | ⟨-, #Hinv, #Hp, #Hc⟩)⟩ HΦ
  · iapply broadcast_chan_receive _ _ _ _ _ $$ Hbc
    iintro ⟨#Hq, -⟩
    iapply HΦ
    iapply HQ $$ Hq
  · iapply closed_chan_receive $$ Hinv
    iapply HΦ
    iframe #

/-- Variant of `ownBroadcastChan_nonblocking_receive` (for `Unknown`) that hands out the
broadcast proposition directly (no later credit needed). -/
theorem broadcast_chan_nonblocking_receive_Q (ch : GoChan) (γ : ChanNames) (Q : IProp GF)
    (Φ : Unit → Bool → IProp GF) (Φnotready : IProp GF) :
    ⊢ ownBroadcastChan ch γ Q .Unknown -∗
      ((□ Q -∗ Φ () false) ∧ Φnotready) -∗
      nonblockingRecvAuAlt γ Unit Φ Φnotready := by
  iintro Hown HΦ
  icases ownBroadcastChan_open _ _ _ _ $$ Hown with ⟨%γch, #Hint, -⟩
  ihave #Hinv := isBroadcastChanInternal_inv _ _ _ _ $$ Hint
  unfold nonblockingRecvAuAlt
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold broadcastInv
  icases Hi with ⟨%st, Hch, Hs⟩
  iexists st
  iframe Hch
  rcases st with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals dsimp only
  case Idle =>
    iintro Hch
    imod Hmask with -
    icases HΦ with ⟨-, HΦ⟩
    imod Hclose $$ [Hch Hs] with -
    · inext; iexists .Idle; dsimp only; iframe
    imodintro
    iexact HΦ
  case RcvPending =>
    iintro Hch
    imod Hmask with -
    icases HΦ with ⟨-, HΦ⟩
    imod Hclose $$ [Hch Hs] with -
    · inext; iexists .RcvPending; dsimp only; iframe
    imodintro
    iexact HΦ
  case Closed.nil =>
    icases Hs with ⟨#HQ, #Hs⟩
    iintro Hch
    imod Hmask with -
    icases HΦ with ⟨HΦ, -⟩
    imod Hclose $$ [Hch] with -
    · inext; iexists .Closed []; dsimp only; iframe Hch
      isplitl []
      · imodintro; iexact HQ
      · iexact Hs
    imodintro
    iapply HΦ $$ HQ
  all_goals (iexfalso; iexact Hs)

theorem isContextDone_nonblocking_receive (s : ContextDesc (IProp GF)) (ch : GoChan)
    (γch : ChanNames) (Φ : Unit → Bool → IProp GF) (Φnotready : IProp GF) :
    ⊢ isContextDone s ch γch -∗
      ((□ s.PDone ∗ ContextClosed s.Done_gn -∗ Φ () false) ∧ Φnotready) -∗
      nonblockingRecvAuAlt γch Unit Φ Φnotready := by
  rw [isContextDone_unseal]; unfold isContextDoneDef
  iintro ⟨-, (⟨%Q, #Hbc, #HQ⟩ | ⟨-, #Hinv, #Hp, #Hc⟩)⟩ HΦ
  · iapply broadcast_chan_nonblocking_receive_Q _ _ _ _ _ $$ Hbc
    isplit
    · iintro #Hq
      icases HΦ with ⟨HΦ, -⟩
      iapply HΦ
      iapply HQ $$ Hq
    · icases HΦ with ⟨-, HΦ⟩
      iexact HΦ
  · iapply closed_chan_nonblocking_receive $$ Hinv
    icases HΦ with ⟨HΦ, -⟩
    iapply HΦ
    iframe #

/-- The Done proposition can be weakened. -/
theorem isContextDone_weaken (s : ContextDesc (IProp GF)) (P' : IProp GF) (ch : GoChan)
    (γch : ChanNames) :
    ⊢ □ (s.PDone -∗ P') -∗ isContextDone s ch γch -∗
      isContextDone { s with PDone := P' } ch γch := by
  rw [isContextDone_unseal]; unfold isContextDoneDef
  iintro #HP ⟨#Hd, (⟨%Q, #Hbc, #HQ⟩ | ⟨#Hch, #Hinv, #Hp, #Hc⟩)⟩
  · isplitl []
    · iexact Hd
    ileft
    iexists Q
    isplitl []
    · iexact Hbc
    imodintro
    iintro #Hq
    icases HQ $$ Hq with ⟨#Hp, #Hc⟩
    isplitl []
    · imodintro; iapply HP $$ Hp
    · iexact Hc
  · isplitl []
    · iexact Hd
    iright
    iframe #
    imodintro; iapply HP $$ Hp

theorem isContext_weaken (c : GoInterfaceOk) (s : ContextDesc (IProp GF)) (P' : IProp GF) :
    ⊢ □ (s.PDone -∗ P') -∗ isContext c s -∗ isContext c { s with PDone := P' } := by
  unfold isContext isContextDef
  iintro #HP ⟨#HDeadline, #HDone, #HErr, #HValue, #HErrDone, #HDoneFresh, #HParentCC, #Hcci⟩
  isplitl []
  · iexact HDeadline
  isplitl []
  · imodintro
    iintro %Φ - HΦ
    iapply HDone
    · itrivial
    inext
    iintro %ch %γch #Hch
    iapply HΦ
    iapply isContextDone_weaken $$ HP Hch
  isplitl []
  · iintro %cl
    imodintro
    iintro %Φ Hpre HΦ
    ihave #HErr' := HErr $$ %cl
    iapply HErr' $$ Hpre
    inext
    iintro %err Herr
    iapply HΦ
    cases cl
    case Done => iexact Herr
    all_goals
      dsimp only
      by_cases herr : err = interface.nil
      · simp only [herr, ↓reduceIte]; itrivial
      · simp only [herr, ↓reduceIte]
        icases Herr with ⟨#Hp, #Hc⟩
        isplitl []
        · imodintro; iapply HP $$ Hp
        · iexact Hc
  isplitl []
  · iexact HValue
  isplitl []
  · iexact HErrDone
  isplitl []
  · imodintro
    iintro %ch #Hd
    iapply HDoneFresh $$ Hd
  iframe #

/-- The lock invariant's half of the done cell: `none` (own half) or `some ch` (discarded). -/
def doneFrag (γ : ContextNames) (od : Option GoChan) : IProp GF :=
  match od with
  | none => dghostVar γ.doneGn (.own (1 : Qp).half) (none : Option GoChan)
  | some ch => dghostVar γ.doneGn .discard (some ch)

/-- The lock invariant's half of the closed flag. -/
def closedFrag (γ : ContextNames) (closed : Bool) : IProp GF :=
  if closed then ContextClosed γ else dghostVar γ.closedGn (.own (1 : Qp).half) false

theorem isContextDone_of_broadcast (γ : ContextNames) (P : IProp GF) (ch : GoChan)
    (γch : ChanNames) :
    ⊢ dghostVar γ.doneGn .discard (some ch) -∗
      ownBroadcastChan ch γch iprop(P ∗ ContextClosed γ) .Unknown -∗
      isContextDone (cdesc γ P) ch γch := by
  rw [isContextDone_unseal]; unfold isContextDoneDef cdesc
  iintro #Hd #Hbc
  isplitl []
  · iexact Hd
  ileft
  iexists iprop(P ∗ ContextClosed γ)
  isplitl []
  · iexact Hbc
  imodintro
  iintro #⟨Hp, Hc⟩
  isplitl []
  · imodintro; iexact Hp
  · iexact Hc

theorem isChan_ne_nil (ch : GoChan) (γ : ChanNames) :
    isChan (GF := GF) ch γ Unit ⊢ ⌜ch ≠ chan.nil⌝ := by
  rw [isChan_unseal]
  iintro H
  iNamed H
  ipureintro; exact Hnotnull

theorem backgroundCtx_ne_stopCtx : context.backgroundCtx.ty ≠ context.stopCtx.ty := by
  unfold context.backgroundCtx.ty context.stopCtx.ty
  intro h; injection h with h1; simp at h1

theorem ptrCancelCtx_ne_stopCtx :
    go.GoType.PointerType context.cancelCtx.ty ≠ context.stopCtx.ty := by
  unfold context.stopCtx.ty
  intro h; cases h

/-- The context `Background()` returns: a `backgroundCtx{}` as a `Context`. Its `Done()` is
`nil` (it is never canceled), so it is not an `isContext`; `wp_WithCancel_Background` derives a
cancelable context from it. -/
abbrev backgroundCtxVal : GoInterfaceOk :=
  interface.mk backgroundCtx.ty #(zero_val backgroundCtx)

/-- `child` as a key of a `children` map (`canceler`) is safe (comparable). -/
instance safeMapKey_cancelCtx (c : Loc) :
    SafeMapKey (GF := GF) context.canceler.ty
      (interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c : GoInterface) :=
  safeMapKey_interface_pointer _ _ _

/-- A `*timerCtx` as a key of a `children` map is safe (comparable). -/
instance safeMapKey_timerCtx (c : Loc) :
    SafeMapKey (GF := GF) context.canceler.ty
      (interface.mkOk (go.GoType.PointerType context.timerCtx.ty) #c : GoInterface) :=
  safeMapKey_interface_pointer _ _ _

/-- A parent context in the scope of these specs: `Background()`, or a context (`isContext`). -/
def isParentCtx (parent : GoInterfaceOk) : IProp GF :=
  iprop(⌜parent = backgroundCtxVal⌝ ∨ ∃ s, isContext parent s)

instance isParentCtx_pers (parent : GoInterfaceOk) : Persistent (isParentCtx (GF := GF) parent) := by
  unfold isParentCtx; infer_instance

theorem cancelCtxLockInv_closed (c : Loc) (γ : ContextNames) (P R : IProp GF) (x : GoChan)
    (cause : GoError) :
    ⊢ ContextClosed γ -∗ dghostVar γ.doneGn .discard (some x) -∗
      structFieldRef context.cancelCtx go!"children" c ↦ map.nil -∗
      structFieldRef context.cancelCtx go!"cause" c ↦ cause -∗ R -∗
      cancelCtxLockInv c γ P R := by
  iintro #Hcl #Hd Hch Hca HR
  unfold cancelCtxLockInv
  iexists map.nil, cause, some x, true
  simp only [↓reduceIte, named]
  iframe
  iframe #

/-- The `Context` field of a `*cancelCtx` (its parent, written once by `propagateCancel`). -/
abbrev ctxField [GoSemanticsFunctions] (c : Loc) : Loc :=
  structFieldRef context.cancelCtx go!"Context" c

theorem isContextDone_doneGn (s : ContextDesc (IProp GF)) (ch : GoChan) (γch : ChanNames) :
    isContextDone s ch γch ⊢ dghostVar s.Done_gn.doneGn .discard (some ch) := by
  rw [isContextDone_unseal]; unfold isContextDoneDef
  iintro ⟨$, -⟩

/-- Once the Done channel `ch` of a `*cancelCtx` is determined, it is not `closedchan` or the
context is done (`doneFresh`, from the invariant). -/
theorem cancelCtx_doneFresh (c : Loc) (γ : ContextNames) (P : IProp GF) (ch : GoChan) :
    ⊢ isCancelCtxOf c γ P -∗ dghostVar γ.doneGn .discard (some ch) -∗ |={⊤}=>
      doneFreshT γ ch := by
  iintro #Hc #Hd
  iunfold isCancelCtxOf at Hc
  icases Hc with ⟨%R, -, #Hinv, -⟩
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  ihave Hx : ▷ (cancelCtxInv c γ P ∗ doneFreshT γ ch) $$ [Hi]
  · inext
    unfold cancelCtxInv
    icases Hi with ⟨%od, %e, Hdone, Hdg, Herr, Hcg⟩
    cases od with
    | none =>
      dsimp only
      ihave %h := dghostVar_agree _ _ _ _ _ $$ Hd Hdg
      cases h
    | some ch' =>
      icases Hdg with ⟨%γch, #Hd', #Hfr⟩
      ihave #Hdd' := isContextDone_doneGn _ _ _ $$ Hd'
      ihave %h := dghostVar_agree _ _ _ _ _ $$ Hd Hdd'
      cases h
      isplitl [Hdone Herr Hcg]
      · iexists (some ch), e; iframe; iexists γch; iframe #
      unfold doneFresh doneFreshT
      icases Hfr with (#Hf | ⟨-, #Hcl⟩)
      · ileft; iexact Hf
      · iright; iexact Hcl
  icases Hx with ⟨Hi, >#Hfr⟩
  imod Hclose $$ Hi with -
  imodintro
  iexact Hfr

theorem ownMap_not_nil_dup (mref : Loc) (m : GMap GoInterface Unit) :
    (ownMap mref (DFrac.own 1) m : IProp GF) ⊢ ownMap mref (DFrac.own 1) m ∗ ⌜mref ≠ map.nil⌝ := by
  rw [ownMap_unseal]; unfold ownMapDef
  iintro H
  iNamed H
  icases heapPointsto_non_null_dup _ _ _ $$ Hown with ⟨Hown, %h⟩
  isplitl
  · iexists mv, ps
    simp only [named]
    iframe
    ipureintro; exact Hrepr
  · ipureintro; exact h

/-- A `childCancelSpec` that needs nothing of the parent's Done proposition holds for any. -/
theorem childCancelSpec_true (Q : IProp GF) (k : GoInterface) :
    childCancelSpec iprop(True) k ⊢ childCancelSpec Q k := by
  cases k with
  | nil => simp only [childCancelSpec]; iintro H; iexact H
  | ok ki =>
    simp only [childCancelSpec]
    iintro #H
    imodintro
    iintro %err %cause %Φ %herr #- HΦ
    iapply H $$ %err %cause %Φ %herr [] HΦ
    imodintro; itrivial

/-- A new `*cancelCtx` (all fields zero) with Done proposition `P` and extra lock resource
`R`: fresh ghost names `γ`, its invariant and the lock invariant of `c.mu`; the `Context` field
is left out, for `propagateCancel` to set. -/
theorem cancelCtx_alloc (c : Loc) (P R : IProp GF) :
    ⊢ isClosedchanInit -∗ c ↦ (zero_val context.cancelCtx) -∗ R -∗ |={⊤}=>
      ∃ γ : ContextNames, isCancelCtxOfR c γ P R ∗ ctxField c ↦ (interface.nil : GoInterface) := by
  iintro #Hcci Hc HRes
  iStructNamedPrefix Hc "F"
  imod dghostVar_alloc (GF := GF) (none : Option GoChan) with ⟨%gd, Hgd⟩
  icases dghostVar_split _ _ (.own (1 : Qp).half) (.own (1 : Qp).half) $$ [Hgd] with ⟨Hgd1, Hgd2⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hgd
  imod dghostVar_alloc (GF := GF) false with ⟨%gc, Hgc⟩
  icases dghostVar_split _ _ (.own (1 : Qp).half) (.own (1 : Qp).half) $$ [Hgc] with ⟨Hgc1, Hgc2⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hgc
  imod inv_alloc cancelCtxN ⊤ (cancelCtxInv c ⟨gd, gc⟩ P) $$ [Fdone Ferr Hgd1 Hgc1]
    with #Hinv
  · inext
    unfold cancelCtxInv
    iexists none, GoInterface.nil
    rw [ite_eq_left rfl]
    dsimp only [doneAny]
    iframe Hgd1 Hgc1
    isplitl [Fdone]
    · iapply (sync.atomic.ownValue_zero _ _).1; iexact Fdone
    · iapply (sync.atomic.ownValue_zero _ _).1; iexact Ferr
  ihave HL : cancelCtxLockInv c ⟨gd, gc⟩ P R $$ [Fchildren Fcause Hgd2 Hgc2 HRes]
  · unfold cancelCtxLockInv
    iexists (zero_val context.cancelCtx).children', (zero_val context.cancelCtx).cause', none,
      false
    simp only [Bool.false_eq_true, ↓reduceIte, named]
    iframe
    simp only [childrenInv]
    ileft; ipureintro; rfl
  imod sync.init_Mutex (cancelCtxLockInv c ⟨gd, gc⟩ P R) ⊤ _ $$ Fmu HL with #Hmu
  iexists ⟨gd, gc⟩
  iframe FContext
  unfold isCancelCtxOfR; iframe #

/-- The spec of `parent.Deadline()`, returning the deadline `dl`. -/
def deadlineSpec (parent : GoInterfaceOk) (dl : Option time.Time) : IProp GF :=
  iprop(□ (∀ Φ : val → IProp GF, True -∗
      ▷ (True -∗ Φ (PairV #(dl.getD (zero_val time.Time))
                          #(match dl with | none => false | some _ => true))) -∗
      WP (App (Val #(methods parent.ty go!"Deadline" parent.v)) (Val #())) {{ Φ }}))

instance deadlineSpec_pers (parent : GoInterfaceOk) (dl : Option time.Time) :
    Persistent (deadlineSpec (GF := GF) parent dl) := by
  unfold deadlineSpec; infer_instance

theorem deadlineSpec_isContext (parent : GoInterfaceOk) (s : ContextDesc (IProp GF)) :
    isContext parent s ⊢ deadlineSpec parent s.Deadline := by
  unfold isContext isContextDef deadlineSpec
  iintro ⟨#HDeadline, -⟩
  iexact HDeadline

/-- The spec of a cancel function: given `□ P`, it cancels the context with ghost names `γ`. -/
def cancelSpec (cancel : GoFunc) (γ : ContextNames) (P : IProp GF) : IProp GF :=
  iprop(□ (∀ Φ : val → IProp GF, □ P -∗ ▷ (ContextClosed γ -∗ Φ #()) -∗
    WP (App (Val #cancel) (Val #())) {{ Φ }}))

instance cancelSpec_pers (cancel : GoFunc) (γ : ContextNames) (P : IProp GF) :
    Persistent (cancelSpec (GF := GF) cancel γ P) := by
  unfold cancelSpec; infer_instance

theorem cancelSpec_weaken (cancel : GoFunc) (γ : ContextNames) (P P' : IProp GF) :
    ⊢ □ (P' -∗ P) -∗ cancelSpec cancel γ P -∗ cancelSpec cancel γ P' := by
  unfold cancelSpec
  iintro #HP #Hc
  imodintro
  iintro %Φ #Hp' HΦ
  iapply Hc $$ [] HΦ
  imodintro; iapply HP $$ Hp'

/-- The cancel-function spec of `wp_WithCancel` without its `ContextClosed` postcondition (the
form used before it gave `ContextClosed`). -/
theorem cancel_spec_forget (cancel : GoFunc) (γ : ContextNames) (P : IProp GF) :
    (□ (∀ Φ : val → IProp GF, □ P -∗ ▷ (ContextClosed γ -∗ Φ #()) -∗
        WP (App (Val #cancel) (Val #())) {{ Φ }}) : IProp GF) ⊢
      □ (∀ Φ : val → IProp GF, □ P -∗ ▷ (True -∗ Φ #()) -∗
        WP (App (Val #cancel) (Val #())) {{ Φ }}) := by
  iintro #Hc
  imodintro
  iintro %Φ #Hp HΦ
  iapply Hc $$ Hp
  inext
  iintro -
  iapply HΦ $$ []
  itrivial

/-- The `cancelCtx` embedded in the `*timerCtx` `c`. -/
abbrev tcc [GoSemanticsFunctions] (c : Loc) : Loc :=
  structFieldRef context.timerCtx go!"cancelCtx" c

/-- The extra lock resource of a `*timerCtx` `c` (`cancelCtxLockInv`): its `timer`, which
`c.mu` protects: `nil`, or a timer made by `AfterFunc`. -/
def timerR (c : Loc) : IProp GF :=
  iprop(∃ tm : Loc, structFieldRef context.timerCtx go!"timer" c ↦ tm ∗
    (⌜tm = Loc.null⌝ ∨ time.isFuncTimer tm))

theorem timerCtx_ne_stopCtx :
    go.GoType.PointerType context.timerCtx.ty ≠ context.stopCtx.ty := by
  unfold context.stopCtx.ty
  intro h; cases h

end wps

end context

end Perennial
