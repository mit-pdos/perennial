/-
Specifications for Go's `context` package.

Proved: `wp_Background`; `wp_WithCancel_Background` (`WithCancel(Background())`) and
`wp_WithCancel` for a parent that is itself a `*cancelCtx` made by `WithCancel`
(`isCancelCtxCtx`); the `*cancelCtx` methods (`wp_cancelCtx_Done`, `wp_cancelCtx_Err`,
`wp_cancelCtx_Value`, `wp_cancelCtx_cancel`); `propagateCancel` for these two kinds of parents
(`wp_propagateCancel_background`, `wp_propagateCancel_cancelCtx`); `wp_withCancel`,
`wp_WithCancel_gen`, `wp_removeChild`; `wp_parentCancelCtx` (any context),
`wp_parentCancelCtx_background`, `wp_parentCancelCtx_self`; `wp_Cause`; and `wp_WithDeadline` /
`wp_WithTimeout` from the spec of `WithDeadlineCause`.

Not proved:
* `wp_WithDeadlineCause` (`sorry`): it calls `time.Time.Before`, `time.AfterFunc` and (in
  `timerCtx.cancel`) `Timer.Stop`, which are neither translated (`Perennial/Code/time.toml`) nor
  axiomatized.
* `WithCancel` of other parents: `propagateCancel`'s remaining branches, for a parent with an
  `AfterFunc` method (`parent.(afterFuncer)`) and the goroutine for any other parent, need
  method-set facts (`methodSet` is uninterpreted in the model, so the type assertion to
  `afterFuncer` cannot be decided) and a spec of the parent's `AfterFunc`. For the parents in
  scope, the proofs show these branches are not taken: `Background()`'s `Done()` is `nil`, and a
  `*cancelCtx` parent is found by `parentCancelCtx` (`wp_parentCancelCtx_self`).

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
* `isInit` (needs `[AllG GF]`): `"#Hclosedchan"`: the global `closedchan` holds a fixed channel,
  which is closed (an invariant holds its state `Closed []`; `init` closes it); `"#HCanceled"`:
  the global `Canceled` holds a fixed typed error. Go never writes either after initialization.
  `parentCancelCtx` compares `parent.Done()` with `closedchan`, and `cancel` stores it.
* `isTypedErr e`: `e` is a non-nil error whose dynamic type is in `error`'s type set (so
  `e.(error)`, in `cancelCtx.Err`, succeeds). True of every Go error; tracked since the model has
  no method-set facts (`Canceled`'s is assumed in `isInit`).
* `isContext` includes `"#HValue"`, the spec of `c.Value(&cancelCtxKey)`: the result, if it
  is a `*cancelCtx`, is a valid one (`isCancelCtx`). `Cause`, `parentCancelCtx` (and through
  it `removeChild`) call `Value(&cancelCtxKey)` to find the innermost `*cancelCtx`.
* `wp_WithDeadlineCause`, `wp_WithDeadline`: the deadline is an existential `some d'` with
  `d' = d ∨ parent_desc.Deadline = some d'`, since when the parent's deadline is earlier,
  `WithDeadlineCause` returns `WithCancel(parent)`.

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
public import Perennial.Proof.sync.atomic
public import Perennial.Proof.sync
public import Perennial.Proof.time
public import Perennial.Proof.errors
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
structure ContextDesc [FfiSyntax] (PROP : Type) where
  mk ::
  Values : GMap GoInterface GoInterface
  Deadline : Option time.Time
  Done_gn : ContextNames
  PDone : PROP

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- Namespace of the invariant saying that `closedchan` is closed. -/
def closedchanN : Namespace := nroot .@ "context.closedchan"

/-- `e` is a non-nil error whose dynamic type is in the type set of `error` (so the type
assertion `e.(error)` succeeds). Every error value has this property in Go; the model has no
method-set facts (`methodSet` is uninterpreted), so it is tracked explicitly. -/
def isTypedErr [GoSemanticsFunctions] (e : GoInterface) : Prop :=
  match e with
  | .ok ii => go.typeSetContains ii.ty go.error = true
  | .nil => False

theorem isTypedErr_ne_nil [GoSemanticsFunctions] {e : GoInterface} (h : isTypedErr e) : e ≠ interface.nil := by
  cases e <;> simp_all [isTypedErr]

/-- The package invariant:
* `"Hgoroutines"`: the `goroutines` counter;
* `"#Hclosedchan"`: the global `closedchan` holds a fixed channel, which is closed (`init`
  closes it): an invariant holds its channel state `Closed []`;
* `"#HCanceled"`: the global `Canceled` holds a fixed error (`errors.New("context
  canceled")`), whose type implements `error` (`isTypedErr`). Go never writes `closedchan`
  or `Canceled` after initialization. -/
abbrev isInit : IProp GF :=
  iprop("Hgoroutines" ∷
    inv nroot (∃ g, sync.atomic.ownInt32 (globalAddr context.goroutines) (DFrac.own 1) g) ∗
  "#Hclosedchan" ∷ (∃ (ch : GoChan) (γ : ChanNames), globalAddr context.closedchan ↦□ ch ∗
    isChan ch γ Unit ∗ inv closedchanN (ownChan γ Unit (.Closed []))) ∗
  "#HCanceled" ∷ (∃ e : GoInterface, globalAddr context.Canceled ↦□ e ∗ ⌜isTypedErr e⌝) ∗
  "_" ∷ True)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.context :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.context :=
  build_get_is_pkg_init_wf

end init

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

open ContextDesc

theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.context ⊢ isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.context

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
`c` has a Done channel (`cancel` stores `closedchan` if there is none). -/
def cancelCtxLockInv (c : Loc) (γ : ContextNames) (P : IProp GF) : IProp GF :=
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
           else ∃ γch, ownBroadcastChan ch γch iprop(P ∗ ContextClosed γ) .Pending))))

/-- `c` is a (shared) `*cancelCtx` with ghost names `γ` and Done proposition `P`. -/
def isCancelCtxOf (c : Loc) (γ : ContextNames) (P : IProp GF) : IProp GF :=
  iprop("#Hmu" ∷ sync.isMutex (structFieldRef context.cancelCtx go!"mu" c)
      (cancelCtxLockInv c γ P) ∗
    "#Hinv" ∷ inv cancelCtxN (cancelCtxInv c γ P))

instance isCancelCtxOf_pers (c : Loc) (γ : ContextNames) (P : IProp GF) :
    Persistent (isCancelCtxOf c γ P) := by
  unfold isCancelCtxOf; infer_instance

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
      WP (App (Val #(methods c.ty go!"Value" c.v)) (Val #cancelCtxKeyAny)) {{ Φ }}))

/-- `c` is a valid context described by `s` (not sealed). See the file header:
* `"#HDone"` returns some channel `ch` with `isContextDone s ch γch`, which carries the
  broadcast-channel knowledge about the Done channel.
* `"#HErr"` takes `ContextClosed s.Done_gn` (precondition, only for `cl = Done`) and gives
  `□ s.PDone ∗ ContextClosed s.Done_gn` (postcondition, for a non-nil error).
* `"#HValue"` only specifies the key `&cancelCtxKey`; the `Values` field of `ContextDesc` is
  unused. -/
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
  iintro #HP ⟨#HDeadline, #HDone, #HErr, #HValue⟩
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
  · iexact HValue

/-! ### The `atomic.Value` cells of a `*cancelCtx` -/

/-- The lock invariant's half of the done cell: `none` (own half) or `some ch` (discarded). -/
def doneFrag (γ : ContextNames) (od : Option GoChan) : IProp GF :=
  match od with
  | none => dghostVar γ.doneGn (.own (1 : Qp).half) (none : Option GoChan)
  | some ch => dghostVar γ.doneGn .discard (some ch)

/-- `c.done.Load()` without the lock: `nil`, or a determined Done channel. -/
theorem wp_done_Load (c : Loc) (γ : ContextNames) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P }}
      (App (Val (structFieldRef context.cancelCtx go!"done" c @!!
        go.GoType.PointerType sync.atomic.Value.ty @!! go!"Load")) (Val #()))
    {{ (od : Option GoChan), RET #(doneAny od);
        match od with
        | none => iprop(True)
        | some ch => ∃ γch, isContextDone (cdesc γ P) ch γch ∗ doneFresh γ P ch }} := by
  iintro %Φ ⟨#Hpkg, #Hc⟩ HΦ
  unfold isCancelCtxOf
  iNamed Hc
  iapply sync.atomic.Value.wp_Load _ (DFrac.own 1)
  · iPkgInit
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold cancelCtxInv
  icases Hi with ⟨%od, %e, Hdone, Hdg, Herr, Hcg⟩
  iexists doneAny od
  iframe Hdone
  iintro Hdone
  imod Hmask with -
  cases od with
  | none =>
    imod Hclose $$ [Hdone Hdg Herr Hcg] with -
    · inext; iexists none, e; iframe
    imodintro
    iapply HΦ $$ %none
    itrivial
  | some ch =>
    icases Hdg with ⟨%γch, #Hd, #Hfr⟩
    imod Hclose $$ [Hdone Herr Hcg] with -
    · inext; iexists (some ch), e; iframe; iexists γch; iframe #
    imodintro
    iapply HΦ $$ %(some ch)
    iexists γch; iframe #

/-- `c.done.Load()` given the lock invariant's half of the done cell, which determines the
result. -/
theorem wp_done_Load_frag (c : Loc) (γ : ContextNames) (P : IProp GF) (od : Option GoChan) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗ doneFrag γ od }}
      (App (Val (structFieldRef context.cancelCtx go!"done" c @!!
        go.GoType.PointerType sync.atomic.Value.ty @!! go!"Load")) (Val #()))
    {{ RET #(doneAny od); doneFrag γ od ∗
        match od with
        | none => iprop(True)
        | some ch => ∃ γch, isContextDone (cdesc γ P) ch γch ∗ doneFresh γ P ch }} := by
  iintro %Φ ⟨#Hpkg, #Hc, Hf⟩ HΦ
  unfold isCancelCtxOf
  iNamed Hc
  iapply sync.atomic.Value.wp_Load _ (DFrac.own 1)
  · iPkgInit
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold cancelCtxInv
  icases Hi with ⟨%od', %e, Hdone, Hdg, Herr, Hcg⟩
  ihave %Heq : ⌜od' = od⌝ $$ [Hdg Hf]
  · cases od' <;> cases od <;> unfold doneFrag <;> dsimp only
    · ipureintro; rfl
    · ihave %h := dghostVar_agree _ _ _ _ _ $$ Hdg Hf
      ipureintro; cases h
    · icases Hdg with ⟨%γch, Hd, -⟩
      rw [isContextDone_unseal]; unfold isContextDoneDef cdesc
      icases Hd with ⟨Hd, -⟩
      ihave %h := dghostVar_agree _ _ _ _ _ $$ Hd Hf
      ipureintro; cases h
    · icases Hdg with ⟨%γch, Hd, -⟩
      rw [isContextDone_unseal]; unfold isContextDoneDef cdesc
      icases Hd with ⟨Hd, -⟩
      ihave %h := dghostVar_agree _ _ _ _ _ $$ Hd Hf
      ipureintro; rw [h]
  subst Heq
  iexists doneAny od'
  iframe Hdone
  iintro Hdone
  imod Hmask with -
  cases od' with
  | none =>
    imod Hclose $$ [Hdone Hdg Herr Hcg] with -
    · inext; iexists none, e; iframe
    imodintro
    iapply HΦ
    iframe Hf
  | some ch =>
    icases Hdg with ⟨%γch, #Hd, #Hfr⟩
    imod Hclose $$ [Hdone Herr Hcg] with -
    · inext; iexists (some ch), e; iframe; iexists γch; iframe #
    imodintro
    iapply HΦ
    iframe Hf
    iexists γch; iframe #

/-- The lock invariant's half of the closed flag. -/
def closedFrag (γ : ContextNames) (closed : Bool) : IProp GF :=
  if closed then ContextClosed γ else dghostVar γ.closedGn (.own (1 : Qp).half) false

/-- `c.err.Load()` without the lock; given `ContextClosed γ` (`cl`), the error is not `nil`. -/
theorem wp_err_Load (c : Loc) (γ : ContextNames) (P : IProp GF) (cl : Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗
        (if cl then ContextClosed γ else iprop(True)) }}
      (App (Val (structFieldRef context.cancelCtx go!"err" c @!!
        go.GoType.PointerType sync.atomic.Value.ty @!! go!"Load")) (Val #()))
    {{ (e : GoInterface), RET #e; ⌜cl = true → e ≠ interface.nil⌝ ∗
        (if e = interface.nil then iprop(True)
         else iprop(⌜isTypedErr e⌝ ∗ □ P ∗ ContextClosed γ)) }} := by
  iintro %Φ ⟨#Hpkg, #Hc, Hcl⟩ HΦ
  unfold isCancelCtxOf
  iNamed Hc
  iapply sync.atomic.Value.wp_Load _ (DFrac.own 1)
  · iPkgInit
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold cancelCtxInv
  icases Hi with ⟨%od, %e, Hdone, Hdg, Herr, Hcg⟩
  iexists e
  iframe Herr
  iintro Herr
  imod Hmask with -
  by_cases he : e = interface.nil
  · subst he
    cases cl
    · imod Hclose $$ [Hdone Hdg Herr Hcg] with -
      · inext; iexists od, GoInterface.nil; iframe
      imodintro
      iapply HΦ
      rw [ite_eq_left rfl]
      isplitl []
      · ipureintro; intro h; cases h
      · itrivial
    · rw [ite_eq_left rfl] at *
      simp only [↓reduceIte, ContextClosed]
      ihave %h := dghostVar_agree _ _ _ _ _ $$ Hcl Hcg
      cases h
  · simp only [he, ↓reduceIte]
    icases Hcg with ⟨%ht, #Hp, #Hc⟩
    imod Hclose $$ [Hdone Hdg Herr] with -
    · inext; iexists od, e; iframe Hdone Hdg Herr
      simp only [he, ↓reduceIte, named]
      iframe #; ipureintro; exact ht
    imodintro
    iapply HΦ
    isplitl []
    · ipureintro; intro _; exact he
    · simp only [he, ↓reduceIte]
      iframe #; ipureintro; exact ht

/-- `c.err.Load()` given the lock invariant's half of the closed flag, which determines whether
the result is `nil`. -/
theorem wp_err_Load_frag (c : Loc) (γ : ContextNames) (P : IProp GF) (closed : Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗ closedFrag γ closed }}
      (App (Val (structFieldRef context.cancelCtx go!"err" c @!!
        go.GoType.PointerType sync.atomic.Value.ty @!! go!"Load")) (Val #()))
    {{ (e : GoInterface), RET #e; closedFrag γ closed ∗
        ⌜closed = false → e = interface.nil⌝ ∗ ⌜closed = true → isTypedErr e⌝ ∗
        □ (⌜closed = true⌝ -∗ P) }} := by
  iintro %Φ ⟨#Hpkg, #Hc, Hf⟩ HΦ
  unfold isCancelCtxOf
  iNamed Hc
  iapply sync.atomic.Value.wp_Load _ (DFrac.own 1)
  · iPkgInit
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold cancelCtxInv
  icases Hi with ⟨%od, %e, Hdone, Hdg, Herr, Hcg⟩
  iexists e
  iframe Herr
  iintro Herr
  imod Hmask with -
  by_cases he : e = interface.nil
  · subst he
    cases closed <;> simp only [closedFrag, ContextClosed, Bool.false_eq_true, ↓reduceIte]
    · imod Hclose $$ [Hdone Hdg Herr Hcg] with -
      · inext; iexists od, GoInterface.nil; iframe Hdone Hdg Herr; rw [ite_eq_left rfl]; iexact Hcg
      imodintro
      iapply HΦ
      iframe Hf
      isplitl []; · ipureintro; intro _; rfl
      isplitl []; · ipureintro; intro h; cases h
      imodintro; iintro %h; cases h
    · ihave %h := dghostVar_agree _ _ _ _ _ $$ Hf Hcg
      cases h
  · simp only [he, ↓reduceIte]
    icases Hcg with ⟨%ht, #Hp, #Hc⟩
    cases closed <;> simp only [closedFrag, Bool.false_eq_true, ↓reduceIte]
    · unfold ContextClosed
      ihave %h := dghostVar_agree _ _ _ _ _ $$ Hf Hc
      cases h
    · imod Hclose $$ [Hdone Hdg Herr] with -
      · inext; iexists od, e; iframe Hdone Hdg Herr
        simp only [he, ↓reduceIte, named]
        iframe #; ipureintro; exact ht
      imodintro
      iapply HΦ
      iframe Hf
      isplitl []; · ipureintro; intro h; cases h
      isplitl []; · ipureintro; intro _; exact ht
      imodintro; iintro -; iexact Hp

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

/-! ### `*cancelCtx` methods -/

theorem wp_cancelCtx_Done (c : Loc) (γ : ContextNames) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P }}
      (App (Val #(methods (go.GoType.PointerType context.cancelCtx.ty) go!"Done" #c)) (Val #()))
    {{ (ch : GoChan) (γch : ChanNames), RET #ch; isContextDone (cdesc γ P) ch γch ∗
        doneFresh γ P ch }} := by
  wp_start as #Hc
  ihave #Hc' := Hc
  iunfold isCancelCtxOf at Hc'
  iNamed Hc'
  iapply wp_with_defer
  iintro %defer Hdefer
  wp_auto
  wp_apply wp_done_Load $$ [$Hc] as %od Hod
  cases od with
  | some ch =>
    icases Hod with ⟨%γch, #Hd, #Hfr⟩
    dsimp only [doneAny]
    wp_auto
    iapply HΦ; iframe #
  | none =>
    dsimp only [doneAny]
    wp_auto
    wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hlk⟩
    unfold cancelCtxLockInv
    icases Hlk with ⟨%children, %cause, %od, %closed, Hchildren, Hcause, Hcl, Hod⟩
    cases od with
    | some ch =>
      icases Hod with ⟨#Hdg, Hpend⟩
      wp_apply wp_done_Load_frag c γ P (some ch) $$ [$Hc Hdg] as ⟨-, Hd⟩
      · unfold doneFrag; iexact Hdg
      icases Hd with ⟨%γch, #Hd, #Hfr⟩
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hchildren Hcause Hcl Hpend]
      · inext; iexists children, cause, some ch, closed; dsimp only; simp only [named]
        iframe; iframe #
      iapply HΦ; iframe #
    | none =>
      icases Hod with ⟨Hdg, %hcl⟩
      wp_apply wp_done_Load_frag c γ P none $$ [$Hc Hdg] as ⟨Hdg, -⟩
      · unfold doneFrag; iexact Hdg
      unfold doneFrag
      dsimp only [doneAny]
      ihave #Hi := isInit_access $$ Hpkg
      icases Hi with ⟨_, ⟨%cch, %γc, #Hcch, #Hcchan, -⟩, _⟩
      ihave #Hcap := chan.isChan_cap _ _ $$ Hcchan
      wp_apply chan.wp_make1_ne (V := Unit) cch γc.chanCap $$ [$Hcap]
        as %ch %γch ⟨#Hch, %hcap, Hoc, %hfresh⟩
      imod alloc_broadcast_chan iprop(P ∗ ContextClosed γ) γch ch $$ Hch Hoc with Hbc
      ihave #Hbcu := ownBroadcastChan_Unknown _ _ _ _ $$ Hbc
      wp_apply_core (sync.atomic.Value.wp_Store _
          (interface.mkOk (go.GoType.ChannelType go.ChanDir.sendrecv (go.GoType.StructType [])) #ch)
          (by simp)) $$ [] [-]
      · iPkgInit
      iinv Hinv with Hi Hclose
      all_goals try solve_ndisj
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hmask
      inext
      unfold cancelCtxInv
      icases Hi with ⟨%od', %e, Hdone, Hdg', Herr, Hcg⟩
      cases od' with
      | some ch' =>
        icases Hdg' with ⟨%γ', Hd', -⟩
        rw [isContextDone_unseal]; unfold isContextDoneDef cdesc
        icases Hd' with ⟨Hd', -⟩
        ihave %h := dghostVar_agree _ _ _ _ _ $$ Hd' Hdg
        cases h
      | none =>
        dsimp only [doneAny]
        iframe Hdone
        iintro Hdone
        imod dghostVar_update_halves (some ch) _ _ _ $$ Hdg Hdg' with ⟨Hdg, Hdg'⟩
        imod dghostVar_persist _ _ _ $$ Hdg with #Hdg
        imod Hmask with -
        imod Hclose $$ [Hdone Herr Hcg] with -
        · inext; iexists (some ch), e; iframe
          iexists γch
          isplitl []
          · iapply isContextDone_of_broadcast $$ Hdg Hbcu
          · unfold doneFresh; ileft; iexists cch; iframe #; ipureintro; exact hfresh
        imodintro
        wp_auto
        subst hcl
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hchildren Hcause Hcl Hbc]
        · inext; iexists children, cause, some ch, false; dsimp only; simp only [named]
          iframe; iframe #; simp only [Bool.false_eq_true, ↓reduceIte]; iexists γch; iframe
        iapply HΦ
        isplitl []
        · iapply isContextDone_of_broadcast $$ Hdg Hbcu
        · unfold doneFresh; ileft; iexists cch; iframe #; ipureintro; exact hfresh

theorem wp_cancelCtx_Err (c : Loc) (γ : ContextNames) (P : IProp GF) (cl : Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗
        (if cl then ContextClosed γ else iprop(True)) }}
      (App (Val #(methods (go.GoType.PointerType context.cancelCtx.ty) go!"Err" #c)) (Val #()))
    {{ (e : GoInterface), RET #e; ⌜cl = true → e ≠ interface.nil⌝ ∗
        (if e = interface.nil then iprop(True)
         else iprop(⌜isTypedErr e⌝ ∗ □ P ∗ ContextClosed γ)) }} := by
  wp_start as ⟨#Hc, Hcl⟩
  wp_auto
  wp_apply wp_err_Load c γ P cl $$ [$Hc $Hcl] as %e ⟨%hcl, He⟩
  by_cases he : e = interface.nil
  · subst he
    wp_auto
    iapply HΦ
    isplitl []
    · ipureintro; exact hcl
    · itrivial
  · simp only [he, ↓reduceIte]
    icases He with ⟨%ht, #Hp, #Hclosed⟩
    cases e with
    | nil => exact absurd rfl he
    | ok ii =>
    wp_auto
    wp_apply wp_cancelCtx_Done $$ [$Hc] as %ch %γch ⟨#Hd, -⟩
    ihave #Hch := isContextDone_is_chan _ _ _ $$ Hd
    wp_bind (App (Val (chan.receive _)) _)
    iapply chan.wp_receive (V := Unit) ch γch $$ Hch
    iintro _
    iapply isContextDone_receive _ _ _ _ $$ Hd
    iintro -
    wp_auto
    erw [ite_eq_left ht]
    wp_auto
    iapply HΦ
    isplitl []
    · ipureintro; intro _; exact he
    · simp only [he, ↓reduceIte, isTypedErr]
      iframe #; ipureintro; exact ht

theorem wp_cancelCtx_Value (c : Loc) (γ : ContextNames) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P }}
      (App (Val #(methods (go.GoType.PointerType context.cancelCtx.ty) go!"Value" #c))
        (Val #cancelCtxKeyAny))
    {{ RET #(interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c); True }} := by
  wp_start as #Hc
  unfold cancelCtxKeyAny
  wp_auto
  iapply HΦ
  itrivial

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

/-! ### `Background()` -/

/-- The context `Background()` returns: a `backgroundCtx{}` as a `Context`. Its `Done()` is
`nil` (it is never canceled), so it is not an `isContext`; `wp_WithCancel_Background` derives a
cancelable context from it. -/
abbrev backgroundCtxVal : GoInterfaceOk :=
  interface.mk backgroundCtx.ty #(zero_val backgroundCtx)

theorem wp_background_Done :
    {{ (True : IProp GF) }}
      (App (Val #(methods backgroundCtx.ty go!"Done" #(zero_val backgroundCtx))) (Val #()))
    {{ RET #chan.nil; True }} := by
  wp_start
  wp_method_call
  wp_auto
  iapply HΦ
  itrivial

theorem wp_background_Deadline :
    {{ (True : IProp GF) }}
      (App (Val #(methods backgroundCtx.ty go!"Deadline" #(zero_val backgroundCtx))) (Val #()))
    {{ RET (PairV #(zero_val time.Time) #false); True }} := by
  wp_start
  wp_method_call
  wp_auto
  iapply HΦ
  itrivial

theorem wp_parentCancelCtx_background :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context }}
      (App (Val (@! context.parentCancelCtx)) (Val #(interface.ok backgroundCtxVal)))
    {{ RET (PairV #Loc.null #false); True }} := by
  wp_start
  ihave #Hi := isInit_access $$ Hpkg
  icases Hi with ⟨_, ⟨%closed, %γcl, #Hclosed, -⟩, _⟩
  wp_alloc par as Hpar
  wp_auto
  wp_apply wp_background_Done
  by_cases h : chan.nil = closed
  · simp only [h, _root_.decide_true]
    wp_auto
    iapply HΦ; itrivial
  · simp only [h, _root_.decide_false]
    wp_auto
    iapply HΦ; itrivial

/-- `child` as a key of a `children` map (`canceler`) is safe (comparable). -/
instance safeMapKey_cancelCtx (c : Loc) :
    SafeMapKey (GF := GF) context.canceler.ty
      (interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c : GoInterface) where
  wp_go_eq_safe_map_key s E Φ := by
    iintro HΦ
    wp_auto
    iapply HΦ

theorem wp_Cause (ctx : GoInterfaceOk) (ctx_desc : ContextDesc (IProp GF)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗
        "#Hctx" ∷ isContext ctx ctx_desc }}
      (App (Val (@! context.Cause)) (Val #(interface.ok ctx)))
    {{ (err : GoInterface), RET #err; True }} := by
  wp_start as #Hctx
  unfold isContext isContextDef
  icases Hctx with ⟨#HDeadline, #HDone, #HErr, #HValue⟩
  wp_auto
  ihave #HErr' := HErr $$ %Broadcast.Unknown
  wp_apply HErr' as %err -
  cases err with
  | nil =>
    wp_auto
    wp_end
  | ok ierr =>
    wp_auto
    unfold cancelCtxKeyAny
    wp_apply HValue as %v #Hv
    cases v with
    | nil =>
      wp_auto
      wp_end
    | ok ii =>
      by_cases hty : ii.ty = go.GoType.PointerType context.cancelCtx.ty
      · simp only [isCancelCtxAny, hty, ↓reduceIte, decide_true]
        icases Hv with ⟨%cc, %hv, #Hcc⟩
        rw [hv]
        unfold isCancelCtx
        icases Hcc with ⟨%γc, %Pc, #Hcc⟩
        unfold isCancelCtxOf
        iNamed Hcc
        wp_auto
        wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hlk⟩
        unfold cancelCtxLockInv
        icases Hlk with ⟨%children, %cause, %od, %closed, Hchildren, Hcause, Hcl, Hod⟩
        wp_auto
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hchildren Hcause Hcl Hod]
        · inext; iexists children, cause, od, closed; iframe
        cases cause with
        | nil =>
          wp_auto
          wp_end
        | ok icause =>
          wp_auto
          wp_end
      · simp only [hty, ↓reduceIte, decide_false]
        wp_auto
        wp_end

/-- The postcondition in the `ok` case is `isCancelCtx ctx` (persistent
knowledge that `ctx` is a valid shared `*cancelCtx`), not `∃ c, ctx ↦ c`. The returned `*cancelCtx` is
shared with every other user of the parent context (its fields are protected
by `ctx.mu` or are atomics), so full ownership of its points-to cannot be
returned. -/
theorem wp_parentCancelCtx (parent : GoInterfaceOk) (parent_desc : ContextDesc (IProp GF)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗
        "#Hctx" ∷ isContext parent parent_desc }}
      (App (Val (@! context.parentCancelCtx)) (Val #(interface.ok parent)))
    {{ (ctx : Loc) (ok : Bool), RET (PairV #ctx #ok);
        if ok then isCancelCtx ctx
        else iprop(⌜ctx = Loc.null⌝) }} := by
  wp_start as #Hctx
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hi := isInit_access $$ Hpkg
  icases Hi with ⟨_, ⟨%closed, %γcl, #Hclosed, -⟩, _⟩
  unfold isContext isContextDef
  icases Hctx with ⟨#HDeadline, #HDone, #HErr, #HValue⟩
  wp_auto
  wp_apply HDone as %done %γdone #Hdone
  by_cases h1 : done = closed
  · simp only [h1, _root_.decide_true]
    wp_auto
    wp_end
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro; trivial
  simp only [h1, _root_.decide_false]
  wp_auto
  by_cases h2 : done = chan.nil
  · simp only [h2, _root_.decide_true]
    wp_auto
    wp_end
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro; trivial
  simp only [h2, _root_.decide_false]
  wp_auto
  unfold cancelCtxKeyAny
  wp_apply HValue as %v #Hv
  cases v with
  | nil =>
    wp_auto
    wp_end
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro; trivial
  | ok ii =>
    by_cases hty : ii.ty = go.GoType.PointerType context.cancelCtx.ty
    · simp only [isCancelCtxAny, hty, ↓reduceIte, _root_.decide_true]
      icases Hv with ⟨%c, %hv, #Hc⟩
      rw [hv]
      wp_auto
      ihave #Hc' : isCancelCtx c $$ []
      · iexact Hc
      unfold isCancelCtx
      icases Hc' with ⟨%γc, %Pc, #Hcc⟩
      wp_apply wp_done_Load $$ [$Hcc] as %och -
      cases och with
      | none =>
        unfold doneAny
        wp_auto
        have h3 : decide (zero_val GoChan = done) = false := by
          simp only [decide_eq_false_iff_not]; exact fun h => h2 h.symm
        simp only [h3]
        wp_auto
        wp_end
        simp only [Bool.false_eq_true, ↓reduceIte]
        ipureintro; trivial
      | some ch =>
        unfold doneAny
        wp_auto
        by_cases h4 : ch = done
        · simp only [h4, _root_.decide_true]
          wp_auto
          wp_end
          simp only [↓reduceIte]
          iexact Hc
        · simp only [h4, _root_.decide_false]
          wp_auto
          wp_end
          simp only [Bool.false_eq_true, ↓reduceIte]
          ipureintro; trivial
    · simp only [hty, ↓reduceIte, _root_.decide_false]
      wp_auto
      wp_end
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro; trivial

/-- A parent context in the scope of these specs: `Background()`, or a context that is a
`*cancelCtx`. -/
def isParentCtx (parent : GoInterfaceOk) : IProp GF :=
  iprop(⌜parent = backgroundCtxVal⌝ ∨
    ∃ s, isContext parent s ∗ ⌜parent.ty = go.GoType.PointerType context.cancelCtx.ty⌝)

instance isParentCtx_pers (parent : GoInterfaceOk) : Persistent (isParentCtx (GF := GF) parent) := by
  unfold isParentCtx; infer_instance

theorem wp_removeChild (parent : GoInterfaceOk) (c : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isParentCtx parent }}
      (App (App (Val (@! context.removeChild)) (Val #(interface.ok parent)))
        (Val #(interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c)))
    {{ RET #(); True }} := by
  wp_start as #Hpar
  unfold isParentCtx
  icases Hpar with (%hbg | ⟨%s, #Hctx, %hty⟩)
  · subst hbg
    wp_auto
    wp_apply wp_parentCancelCtx_background
    iapply HΦ; itrivial
  · have hne : parent.ty ≠ context.stopCtx.ty := by rw [hty]; exact ptrCancelCtx_ne_stopCtx
    wp_auto
    simp only [hne, ↓reduceIte, _root_.decide_false]
    wp_auto
    wp_apply wp_parentCancelCtx parent s $$ [$Hctx] as %p %ok Hp
    cases ok
    · wp_auto
      iapply HΦ; itrivial
    · simp only [↓reduceIte]
      iunfold isCancelCtx at Hp
      icases Hp with ⟨%γp, %Pp, #Hp⟩
      iunfold isCancelCtxOf at Hp
      iNamed Hp
      wp_auto
      wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hlk⟩
      unfold cancelCtxLockInv
      icases Hlk with ⟨%children, %cause, %od, %closed, Hchildren, Hcause, Hcl, Hod⟩
      wp_auto
      by_cases hnil : children = map.nil
      · rw [show decide (children = map.nil) = true from decide_eq_true hnil]
        wp_auto
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hchildren Hcause Hcl Hod]
        · inext; iexists children, cause, od, closed; iframe
        iapply HΦ; itrivial
      · rw [show decide (children = map.nil) = false from decide_eq_false hnil]
        cases closed
        · simp only [Bool.false_eq_true, ↓reduceIte]
          icases Hcl with ⟨Hcg, Hch⟩
          unfold childrenInv
          icases Hch with (%h | ⟨%M, HM, #Hspecs⟩)
          · exact absurd h hnil
          wp_auto
          wp_apply wp_mapDelete $$ [$HM] as HM
          wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hchildren Hcause Hcg HM Hod]
          · inext; iexists children, cause, od, false; simp only [Bool.false_eq_true, ↓reduceIte]
            iframe
            simp only [named]
            iframe Hcg
            iright
            iexists _
            iframe HM
            imodintro
            iintro %k %u %hk
            iapply Hspecs $$ %k %u
            ipureintro
            rw [GMap.lookup_delete_iff] at hk
            split at hk
            · cases hk
            · exact hk
          iapply HΦ; itrivial
        · simp only [↓reduceIte]
          icases Hcl with ⟨-, %h⟩
          exact absurd h hnil

theorem cancelCtxLockInv_closed (c : Loc) (γ : ContextNames) (P : IProp GF) (x : GoChan)
    (cause : GoError) :
    ⊢ ContextClosed γ -∗ dghostVar γ.doneGn .discard (some x) -∗
      structFieldRef context.cancelCtx go!"children" c ↦ map.nil -∗
      structFieldRef context.cancelCtx go!"cause" c ↦ cause -∗
      cancelCtxLockInv c γ P := by
  iintro #Hcl #Hd Hch Hca
  unfold cancelCtxLockInv
  iexists map.nil, cause, some x, true
  simp only [↓reduceIte, named]
  iframe
  iframe #

/-- `c.cancel(rm, err, cause)` for a typed error `err`, given `□ P`: closes `c` (and its Done
channel), cancels `c`'s children (with their stored `childCancelSpec`), and, if `rm`, removes `c`
from its parent's `children` (`removeChild(c.Context, c)`, for a parent of the kinds of
`isParentCtx`). -/
theorem wp_cancelCtx_cancel (c : Loc) (γ : ContextNames) (P : IProp GF) (rm : Bool)
    (err cause : GoInterface) (herr : isTypedErr err) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗ □ P ∗
        (if rm then iprop(∃ parent : GoInterfaceOk,
            structFieldRef context.cancelCtx go!"Context" c ↦□ (interface.ok parent : GoInterface) ∗
            isParentCtx parent)
         else iprop(True)) }}
      (App (App (App (Val #(methods (go.GoType.PointerType context.cancelCtx.ty) go!"cancel" #c))
        (Val #rm)) (Val #err)) (Val #cause))
    {{ RET #(); ContextClosed γ }} := by
  wp_start as ⟨#Hc, #Hp, Hrm⟩
  ihave #Hc' := Hc
  iunfold isCancelCtxOf at Hc'
  iNamed Hc'
  ihave #Hi := isInit_access $$ Hpkg
  icases Hi with ⟨_, ⟨%cch, %γc, #Hcch, #Hcchan, #Hcinv⟩, _⟩
  cases err with
  | nil => exact absurd herr id
  | ok ierr =>
  wp_auto
  cases cause <;> wp_auto
  all_goals
    wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hlk⟩
    unfold cancelCtxLockInv
    icases Hlk with ⟨%children, %cause0, %od, %closed, Hchildren, Hcause, Hcl, Hod⟩
    cases closed
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hcl with ⟨Hcg, Hch⟩
      wp_apply wp_err_Load_frag c γ P false $$ [$Hc Hcg] as %e ⟨Hcg, Hhe⟩
      · unfold closedFrag; simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hcg
      icases Hhe with ⟨%he, -, -⟩
      have he := he (by simp)
      subst he
      wp_auto
      unfold closedFrag
      simp only [Bool.false_eq_true, ↓reduceIte]
      wp_apply_core (sync.atomic.Value.wp_Store _ (interface.ok ierr) (by simp)) $$ [] [-]
      · iPkgInit
      iinv Hinv with Hi Hclose
      all_goals try solve_ndisj
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hmask
      inext
      unfold cancelCtxInv
      icases Hi with ⟨%od', %e, Hdone, Hdg, Herr, Hcg'⟩
      by_cases he : e = interface.nil
      · subst he
        simp only [ite_true]
        iframe Herr
        iintro Herr
        imod dghostVar_update_halves true _ _ _ $$ Hcg Hcg' with ⟨Hcg, Hcg'⟩
        imod dghostVar_persist _ _ _ $$ Hcg with #Hclosed
        imod Hmask with -
        imod Hclose $$ [Hdone Hdg Herr] with -
        · inext; iexists od', interface.ok ierr; iframe
          simp only [named]
          rw [ite_eq_right (by simp)]
          unfold ContextClosed
          iframe #
          ipureintro; exact herr
        imodintro
        wp_auto
        iclear Hcg'
        cases od
        case' none =>
          icases Hod with ⟨Hdgf, -⟩
          wp_apply wp_done_Load_frag c γ P none $$ [$Hc Hdgf] as ⟨Hdgf, -⟩
          · unfold doneFrag; iexact Hdgf
          unfold doneFrag; dsimp only [doneAny]
          wp_apply_core (sync.atomic.Value.wp_Store _
              (interface.mkOk (go.GoType.ChannelType go.ChanDir.sendrecv (go.GoType.StructType [])) #cch)
              (by simp)) $$ [] [-]
          · iPkgInit
          iinv Hinv with Hi Hclose
          all_goals try solve_ndisj
          iapply fupd_mask_intro Std.LawfulSet.empty_subset
          iintro Hmask
          inext
          icases Hi with ⟨%od', %e', Hdone, Hdg, Herr, Hcg'⟩
          cases od'
          case some ch' =>
            icases Hdg with ⟨%γ', Hd', -⟩
            rw [isContextDone_unseal]; unfold isContextDoneDef cdesc
            icases Hd' with ⟨Hd', -⟩
            ihave %h := dghostVar_agree _ _ _ _ _ $$ Hd' Hdgf
            cases h
          dsimp only [doneAny]
          iframe Hdone
          iintro Hdone
          imod dghostVar_update_halves (some cch) _ _ _ $$ Hdgf Hdg with ⟨Hdgf, Hdg⟩
          imod dghostVar_persist _ _ _ $$ Hdgf with #Hdgf
          imod Hmask with -
          imod Hclose $$ [Hdone Herr Hcg'] with -
          · inext; iexists (some cch), e'; iframe
            iexists γc
            isplitl []
            · rw [isContextDone_unseal]; unfold isContextDoneDef cdesc
              isplitl []
              · iexact Hdgf
              iright
              unfold ContextClosed
              iframe #
            · unfold doneFresh; iright; unfold ContextClosed; iframe #
          imodintro
          wp_auto
        case' some ch =>
          icases Hod with ⟨#Hdgf, %γch, Hpend⟩
          wp_apply wp_done_Load_frag c γ P (some ch) $$ [$Hc] as ⟨-, -⟩
          · unfold doneFrag; iexact Hdgf
          dsimp only [doneAny]
          ihave #Hchp := ownBroadcastChan_is_chan _ _ _ _ $$ Hpend
          ihave %hnn := isChan_ne_nil _ _ $$ Hchp
          rw [decide_eq_false hnn]
          wp_auto
          wp_apply wp_broadcast_chan_close ch γch iprop(P ∗ ContextClosed γ) $$ [$Hpend] as -
          · imodintro; unfold ContextClosed; iframe #
        all_goals
          iunfold childrenInv at Hch
          wp_func_lits
          icases Hch with (%hnil | ⟨%M, HM, #Hspecs⟩)
          all_goals first
            | (subst hnil
               wp_auto)
            | (wp_bind (App (App (Val (map.forRange _ _)) _) _)
               iapply (wp_map_for_range (fun _ _ => iprop(∃ (v cv : GoInterface),
                  child_ptr ↦ v ∗ err_ptr ↦ GoInterface.ok ierr ∗ cause_ptr ↦ cv))) $$ HM
               iintro %keys %hkeys
               isplitl [child err cause]
               · iexists _, _; iframe
               isplitl []
               · imodintro
                 iintro %i %key %u ⟨%hk1, %hk2⟩ ⟨%v, %cv, Hchild, Herr, Hcause⟩
                 ihave #Hsp := Hspecs $$ %key %u %hk2
                 cases key with
                 | nil => simp only [childCancelSpec]; iexfalso; iexact Hsp
                 | ok ki =>
                 simp only [childCancelSpec]
                 wp_auto
                 wp_apply Hsp
                 · ipureintro; exact herr
                 · iexact Hp
                 unfold forMapPostcondition
                 iright; ileft
                 isplit
                 · ipureintro; rfl
                 · iexists _, _; iframe
               iintro ⟨%v, %cv, child, err, cause⟩ HM
               wp_auto)
          all_goals
            wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hchildren Hcause]
            · inext
              ihave H := cancelCtxLockInv_closed c γ P _ _ $$ [] Hdgf Hchildren Hcause
              · unfold ContextClosed; iexact Hclosed
              iunfold cancelCtxLockInv at H
              iexact H
            cases rm
            · wp_auto
              iapply HΦ; unfold ContextClosed; iexact Hclosed
            · simp only [↓reduceIte]
              icases Hrm with ⟨%parent, #Hpf, #Hpar⟩
              wp_auto
              wp_apply wp_removeChild parent c $$ [$Hpar]
              iapply HΦ; unfold ContextClosed; iexact Hclosed
      · rw [ite_eq_right he]
        icases Hcg' with ⟨-, -, Hc2⟩
        unfold ContextClosed
        ihave %h := dghostVar_agree _ _ _ _ _ $$ Hcg Hc2
        cases h
    · simp only [↓reduceIte]
      icases Hcl with ⟨#Hclosed, %hch⟩
      wp_apply wp_err_Load_frag c γ P true $$ [$Hc] as %e ⟨-, Hhe⟩
      · unfold closedFrag; simp only [↓reduceIte]; iexact Hclosed
      icases Hhe with ⟨-, %ht, -⟩
      have ht := ht (by simp)
      cases e with
      | nil => exact absurd ht id
      | ok ie =>
      wp_auto
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hchildren Hcause Hod]
      · inext; iexists children, _, od, true; simp only [↓reduceIte, named]; iframe; iframe #
        ipureintro; exact hch
      iapply HΦ $$ Hclosed

/-- The `Context` field of a `*cancelCtx` (its parent, written once by `propagateCancel`). -/
abbrev ctxField [GoSemanticsFunctions] (c : Loc) : Loc :=
  structFieldRef context.cancelCtx go!"Context" c

/-- `c.propagateCancel(Background(), c)`: the parent is never canceled (`Done()` is `nil`). -/
theorem wp_propagateCancel_background (c : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗
        ctxField c ↦ (interface.nil : GoInterface) }}
      (App (App (Val (c @!! go.GoType.PointerType context.cancelCtx.ty @!! go!"propagateCancel"))
        (Val #(interface.ok backgroundCtxVal)))
        (Val #(interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c)))
    {{ RET #(); ctxField c ↦ (interface.ok backgroundCtxVal : GoInterface) }} := by
  wp_start as Hf
  wp_auto
  wp_apply wp_background_Done
  iapply HΦ $$ Hf


theorem isContextDone_doneGn (s : ContextDesc (IProp GF)) (ch : GoChan) (γch : ChanNames) :
    isContextDone s ch γch ⊢ dghostVar s.Done_gn.doneGn .discard (some ch) := by
  rw [isContextDone_unseal]; unfold isContextDoneDef
  iintro ⟨$, -⟩

/-- `c.done.Load()` once the Done channel `ch` is known: it returns `ch`. -/
theorem wp_done_Load_known (c : Loc) (γ : ContextNames) (P : IProp GF) (ch : GoChan)
    (γch : ChanNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗
        isContextDone (cdesc γ P) ch γch }}
      (App (Val (structFieldRef context.cancelCtx go!"done" c @!!
        go.GoType.PointerType sync.atomic.Value.ty @!! go!"Load")) (Val #()))
    {{ RET #(doneAny (some ch)); True }} := by
  iintro %Φ ⟨#Hpkg, #Hc, #Hd⟩ HΦ
  unfold isCancelCtxOf
  iNamed Hc
  iapply sync.atomic.Value.wp_Load _ (DFrac.own 1)
  · iPkgInit
  iinv Hinv with Hi Hclose
  all_goals try solve_ndisj
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold cancelCtxInv
  icases Hi with ⟨%od, %e, Hdone, Hdg, Herr, Hcg⟩
  ihave #Hdd := isContextDone_doneGn _ _ _ $$ Hd
  cases od
  case none =>
    dsimp only
    ihave %h := dghostVar_agree _ _ _ _ _ $$ Hdd Hdg
    cases h
  case some ch' =>
    icases Hdg with ⟨%γ', #Hd2, #Hfr⟩
    ihave #Hdd2 := isContextDone_doneGn _ _ _ $$ Hd2
    ihave %h := dghostVar_agree _ _ _ _ _ $$ Hdd Hdd2
    cases h
    iexists doneAny (some ch)
    iframe Hdone
    iintro Hdone
    imod Hmask with -
    imod Hclose $$ [Hdone Herr Hcg] with -
    · inext; iexists (some ch), e; iframe
      iexists γ'
      iframe #
    imodintro
    iapply HΦ $$ []
    itrivial

/-- `parentCancelCtx(p)` for a `*cancelCtx` `p` whose Done channel `ch` (as returned by an
earlier `p.Done()`) is not `closedchan`: it returns `p`. -/
theorem wp_parentCancelCtx_self (p : Loc) (s : ContextDesc (IProp GF)) (ch cch : GoChan)
    (γch : ChanNames) (hcch : ch ≠ cch) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf p s.Done_gn s.PDone ∗
        isContextDone (cdesc s.Done_gn s.PDone) ch γch ∗ globalAddr context.closedchan ↦□ cch }}
      (App (Val (@! context.parentCancelCtx))
        (Val #(interface.ok (interface.mk (go.GoType.PointerType context.cancelCtx.ty) #p))))
    {{ RET (PairV #p #true); True }} := by
  wp_start as ⟨#Hp, #Hd, #Hcch⟩
  wp_alloc par as Hpar
  wp_pures
  wp_load
  wp_pures
  wp_apply wp_cancelCtx_Done p _ _ $$ [$Hp] as %ch' %γch' ⟨#Hd', -⟩
  ihave %heq := isContextDone_agree (cdesc s.Done_gn s.PDone) ch ch' γch γch' $$ [Hd Hd']
  · iframe #
  subst heq
  ihave #Hch := isContextDone_is_chan _ _ _ $$ Hd
  ihave %hnn := isChan_ne_nil _ _ $$ Hch
  rw [decide_eq_false hcch]
  wp_auto
  rw [decide_eq_false hnn]
  wp_auto
  wp_apply wp_cancelCtx_Value p _ _ $$ [$Hp]
  wp_apply wp_done_Load_known p _ _ ch γch $$ [$Hp $Hd]
  iapply HΦ; itrivial

theorem ownMap_not_nil_dup (mref : Loc) (m : GMap GoInterface Unit) :
    (ownMap mref (DFrac.own 1) m : IProp GF) ⊢ ownMap mref (DFrac.own 1) m ∗ ⌜mref ≠ map.nil⌝ := by
  rw [ownMap_unseal]; unfold ownMapDef
  iintro H
  iNamed H
  icases heapPointsto_non_null_dup _ _ _ $$ Hown with ⟨Hown, %h⟩
  isplitl
  · iexists mv, mp
    simp only [named]
    iframe
    ipureintro; exact ⟨His_map, Hagree, Hdom, Hdefault⟩
  · ipureintro; exact h

/-- The `childCancelSpec` of a `*cancelCtx` child whose Done proposition follows from the
parent's. -/
theorem childCancelSpec_cancelCtx (c : Loc) (γ : ContextNames) (P Q : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗ □ (Q -∗ P) ⊢
      childCancelSpec Q (interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c) := by
  iintro ⟨#Hpkg, #Hc, #HQ⟩
  simp only [childCancelSpec]
  imodintro
  iintro %err %cause %Φ %herr #Hq HΦ
  iapply wp_cancelCtx_cancel c γ P false err cause herr $$ [$Hpkg $Hc]
  · isplitl []
    · imodintro; iapply HQ $$ Hq
    · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  inext; iintro -; iexact HΦ

/-- `c.propagateCancel(parent, c)` for a parent that is a `*cancelCtx` described by `s` whose
Done proposition implies `c`'s: either the parent is already done (then `c` is canceled at once),
or `c` is added to the parent's `children` (with its `childCancelSpec`). -/
theorem wp_propagateCancel_cancelCtx (c : Loc) (γ : ContextNames) (P : IProp GF)
    (parent : GoInterfaceOk) (s : ContextDesc (IProp GF)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗
        ctxField c ↦ (interface.nil : GoInterface) ∗
        (isContext parent s ∗ isCancelCtxCtx parent s ∗ □ (s.PDone -∗ P)) }}
      (App (App (Val (c @!! go.GoType.PointerType context.cancelCtx.ty @!! go!"propagateCancel"))
        (Val #(interface.ok parent)))
        (Val #(interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c)))
    {{ RET #(); ctxField c ↦ (interface.ok parent : GoInterface) }} := by
  wp_start as ⟨#Hc, Hf, #Hctx, #Hcc, #HPP⟩
  iunfold isCancelCtxCtx at Hcc
  icases Hcc with ⟨%p, %hp, #Hp⟩
  subst hp
  ihave #Hi := isInit_access $$ Hpkg
  icases Hi with ⟨_, ⟨%cch, %γc, #Hcch, #Hcchan, #Hcinv⟩, _⟩
  wp_auto
  wp_apply wp_cancelCtx_Done p _ _ $$ [$Hp] as %ch %γch ⟨#Hd, #Hfr⟩
  ihave #Hch := isContextDone_is_chan _ _ _ $$ Hd
  ihave %hnn := isChan_ne_nil _ _ $$ Hch
  rw [decide_eq_false hnn]
  wp_auto
  by_cases hcc : ch = cch
  · subst hcc
    iunfold doneFresh at Hfr
    icases Hfr with (⟨%cch', #Hcch', %hne⟩ | ⟨#Hpd, #Hcl⟩)
    · icombine Hcch Hcch' gives %heq
      exact absurd heq hne
    wp_apply_core chan.wp_select_nonblocking_alt [iprop(False)]
        iprop(c_ptr ↦ c ∗ child_ptr ↦ (interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c : GoInterface) ∗
          parent_ptr ↦ (interface.ok (interface.mk (go.GoType.PointerType context.cancelCtx.ty) #p) : GoInterface) ∗
          ctxField c ↦ (interface.ok (interface.mk (go.GoType.PointerType context.cancelCtx.ty) #p) : GoInterface))
        $$ [HΦ] [c child parent Hf] []
    · iapply BigSepL2.bigSepL2_singleton.2
      iintro ⟨c, child, parent, Hf⟩
      simp only [chan.nonblockingAltClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc
      isplitr
      · ipureintro; rfl
      isplitr
      · iexact Hcchan
      iapply closed_chan_nonblocking_receive $$ Hcinv
      wp_auto
      wp_apply wp_cancelCtx_Err p s.Done_gn s.PDone true $$ [$Hp]
        as %e ⟨%hne, He⟩
      · simp only [↓reduceIte]; iexact Hcl
      have hne := hne rfl
      rw [ite_eq_right hne]
      icases He with ⟨%htyped, -, -⟩
      wp_apply wp_Cause (interface.mk (go.GoType.PointerType context.cancelCtx.ty) #p) s $$ [$Hctx]
        as %cause -
      wp_apply wp_cancelCtx_cancel c γ P false e cause htyped $$ [$Hc] as -
      · isplitl []
        · imodintro; iapply HPP $$ Hpd
        · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      iapply HΦ $$ Hf
    · iframe
    · iintro - Hnr
      icases BigSepL.bigSepL_singleton.1 $$ Hnr with Hfalse
      iexfalso; iexact Hfalse
  wp_apply_core chan.wp_select_nonblocking_alt [iprop(⌜ch ≠ cch⌝)]
      iprop(c_ptr ↦ c ∗ child_ptr ↦ (interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c : GoInterface) ∗
        parent_ptr ↦ (interface.ok (interface.mk (go.GoType.PointerType context.cancelCtx.ty) #p) : GoInterface) ∗
        ctxField c ↦ (interface.ok (interface.mk (go.GoType.PointerType context.cancelCtx.ty) #p) : GoInterface) ∗
        (ctxField c ↦ (interface.ok (interface.mk (go.GoType.PointerType context.cancelCtx.ty) #p) : GoInterface)
          -∗ Φ #()))
      $$ [] [c child parent Hf HΦ] []
  · iapply BigSepL2.bigSepL2_singleton.2
    iintro ⟨c, child, parent, Hf, HΦ⟩
    simp only [chan.nonblockingAltClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γch
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact Hch
    iapply isContextDone_nonblocking_receive _ _ _ _ _ $$ Hd
    isplit
    · iintro ⟨#Hpd, #Hcl⟩
      wp_auto
      wp_apply wp_cancelCtx_Err p s.Done_gn s.PDone true $$ [$Hp]
        as %e ⟨%hne, He⟩
      · simp only [↓reduceIte]; iexact Hcl
      have hne := hne rfl
      rw [ite_eq_right hne]
      icases He with ⟨%htyped, -, -⟩
      wp_apply wp_Cause (interface.mk (go.GoType.PointerType context.cancelCtx.ty) #p) s $$ [$Hctx]
        as %cause -
      wp_apply wp_cancelCtx_cancel c γ P false e cause htyped $$ [$Hc] as -
      · isplitl []
        · imodintro; iapply HPP $$ Hpd
        · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      iapply HΦ $$ Hf
    · iframe; ipureintro; exact hcc
  · iframe
  · iintro ⟨c, child, parent, Hf, HΦ⟩ -
    wp_auto
    wp_apply wp_parentCancelCtx_self p s ch cch γch hcc $$ [$Hp $Hd $Hcch]
    ihave #Hp' := Hp
    iunfold isCancelCtxOf at Hp'
    icases Hp' with ⟨#Hmup, #Hinvp⟩
    wp_apply sync.Mutex.wp_Lock $$ [$Hmup] as ⟨Hlocked, Hlk⟩
    iunfold cancelCtxLockInv at Hlk
    icases Hlk with ⟨%children, %cause, %od, %closed, Hchildren, Hcause, Hcl, Hod⟩
    cases closed
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hcl with ⟨Hcg, Hchs⟩
      wp_apply wp_err_Load_frag p _ _ false $$ [$Hp Hcg] as %e ⟨Hcg, Hhe⟩
      · unfold closedFrag; simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hcg
      icases Hhe with ⟨%he, -, -⟩
      have he := he (by simp)
      subst he
      wp_auto
      iunfold childrenInv at Hchs
      icases Hchs with (%hnil | ⟨%M, HM, #Hspecs⟩)
      · subst hnil
        rw [show decide (map.nil = map.nil) = true from decide_eq_true rfl]
        wp_pures
        wp_apply (wp_map_make1 (K := GoInterface) (V := Unit) context.canceler.ty
          (go.GoType.StructType [])) as %m HM
        wp_apply (wp_mapInsert context.canceler.ty m (∅ : GMap GoInterface Unit)
          (interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c) ()) $$ [$HM] as HM
        ihave #Hcs := childCancelSpec_cancelCtx c γ P s.PDone $$ [$Hpkg $Hc $HPP]
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmup $Hlocked Hchildren Hcause Hcg HM Hod]
        · inext; unfold cancelCtxLockInv
          iexists m, cause, od, false
          simp only [Bool.false_eq_true, ↓reduceIte, named]
          iframe
          unfold closedFrag; simp only [Bool.false_eq_true, ↓reduceIte]
          iframe
          unfold childrenInv
          iright
          iexists _
          iframe HM
          imodintro
          iintro %k %u %hk
          rw [GMap.lookup_insert_eq_iff] at hk
          split at hk
          · rename_i heq; subst heq; iexact Hcs
          · simp at hk
        iapply HΦ $$ Hf
      · icases ownMap_not_nil_dup _ _ $$ HM with ⟨HM, %hnn'⟩
        rw [show decide (children = map.nil) = false from decide_eq_false hnn']
        wp_pures
        wp_auto
        wp_apply (wp_mapInsert context.canceler.ty children M
          (interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c) ()) $$ [$HM] as HM
        ihave #Hcs := childCancelSpec_cancelCtx c γ P s.PDone $$ [$Hpkg $Hc $HPP]
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmup $Hlocked Hchildren Hcause Hcg HM Hod]
        · inext; unfold cancelCtxLockInv
          iexists children, cause, od, false
          simp only [Bool.false_eq_true, ↓reduceIte, named]
          iframe
          unfold closedFrag; simp only [Bool.false_eq_true, ↓reduceIte]
          iframe
          unfold childrenInv
          iright
          iexists _
          iframe HM
          imodintro
          iintro %k %u %hk
          rw [GMap.lookup_insert_eq_iff] at hk
          split at hk
          · rename_i heq; subst heq; iexact Hcs
          · iapply Hspecs $$ %k %u %hk
        iapply HΦ $$ Hf
    · simp only [↓reduceIte]
      icases Hcl with ⟨#Hclosed, %hch⟩
      wp_apply wp_err_Load_frag p _ _ true $$ [$Hp] as %e ⟨-, Hhe⟩
      · unfold closedFrag; simp only [↓reduceIte]; iexact Hclosed
      icases Hhe with ⟨-, %ht, #Hpd⟩
      have ht := ht (by simp)
      cases e with
      | nil => exact absurd ht id
      | ok ie =>
      wp_auto
      erw [ite_eq_left ht]
      wp_auto
      wp_apply wp_cancelCtx_cancel c γ P false (GoInterface.ok ie) cause ht $$ [$Hc] as -
      · isplitl []
        · imodintro; iapply HPP; iapply Hpd; ipureintro; simp
        · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmup $Hlocked Hchildren Hcause Hod]
      · inext; unfold cancelCtxLockInv
        iexists children, cause, od, true; simp only [↓reduceIte, named]; iframe; iframe #
        ipureintro; exact hch
      iapply HΦ $$ Hf

/-- `withCancel(parent)`, given the spec of `c.propagateCancel(parent, c)` for the new `c` (with
`Pre`): allocates the `*cancelCtx` `c` with fresh ghost names `γ` and Done proposition `P`, and
sets its parent. -/
theorem wp_withCancel (parent : GoInterfaceOk) (P Pre : IProp GF)
    (Hprop : ∀ (c : Loc) (γ : ContextNames),
      {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗
          ctxField c ↦ (interface.nil : GoInterface) ∗ Pre }}
        (App (App (Val (c @!! go.GoType.PointerType context.cancelCtx.ty @!! go!"propagateCancel"))
          (Val #(interface.ok parent)))
          (Val #(interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c)))
      {{ RET #(); ctxField c ↦ (interface.ok parent : GoInterface) }}) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ Pre }}
      (App (Val (@! context.withCancel)) (Val #(interface.ok parent)))
    {{ (c : Loc) (γ : ContextNames), RET #c;
        isCancelCtxOf c γ P ∗ ctxField c ↦□ (interface.ok parent : GoInterface) }} := by
  wp_start as Hpre
  wp_auto
  iStructNamedPrefix «$r0» "F"
  imod dghostVar_alloc (GF := GF) (none : Option GoChan) with ⟨%gd, Hgd⟩
  icases dghostVar_split _ _ (.own (1 : Qp).half) (.own (1 : Qp).half) $$ [Hgd] with ⟨Hgd1, Hgd2⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hgd
  imod dghostVar_alloc (GF := GF) false with ⟨%gc, Hgc⟩
  icases dghostVar_split _ _ (.own (1 : Qp).half) (.own (1 : Qp).half) $$ [Hgc] with ⟨Hgc1, Hgc2⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hgc
  imod inv_alloc cancelCtxN ⊤ (cancelCtxInv «$r0_ptr» ⟨gd, gc⟩ P) $$ [Fdone Ferr Hgd1 Hgc1]
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
  ihave HR : cancelCtxLockInv «$r0_ptr» ⟨gd, gc⟩ P $$ [Fchildren Fcause Hgd2 Hgc2]
  · unfold cancelCtxLockInv
    iexists map.nil, GoInterface.nil, none, false
    simp only [Bool.false_eq_true, ↓reduceIte, named]
    iframe
    unfold childrenInv
    ileft; ipureintro; rfl
  imod sync.init_Mutex (cancelCtxLockInv «$r0_ptr» ⟨gd, gc⟩ P) ⊤ _ $$ Fmu HR with #Hmu
  ihave #Hc : isCancelCtxOf «$r0_ptr» ⟨gd, gc⟩ P $$ []
  · unfold isCancelCtxOf; iframe #
  iapply wp_fupd
  wp_apply Hprop «$r0_ptr» ⟨gd, gc⟩ $$ [$Hc FContext Hpre] as HC
  · iframe
  dsimp only [ctxField]
  ipersist HC
  imodintro
  iapply HΦ
  iframe #

/-- The spec of `parent.Deadline()`, returning the deadline `dl`. -/
def deadlineSpec (parent : GoInterfaceOk) (dl : Option time.Time) : IProp GF :=
  iprop(□ (∀ Φ : val → IProp GF, True -∗
      ▷ (True -∗ Φ (PairV #(dl.getD (zero_val time.Time))
                          #(match dl with | none => false | some _ => true))) -∗
      WP (App (Val #(methods parent.ty go!"Deadline" parent.v)) (Val #())) {{ Φ }}))

instance deadlineSpec_pers (parent : GoInterfaceOk) (dl : Option time.Time) :
    Persistent (deadlineSpec (GF := GF) parent dl) := by
  unfold deadlineSpec; infer_instance

theorem deadlineSpec_background : ⊢ deadlineSpec (GF := GF) backgroundCtxVal none := by
  unfold deadlineSpec
  simp only [Option.getD]
  imodintro
  iintro %Φ - HΦ
  iapply wp_background_Deadline
  · itrivial
  inext; iintro -
  iapply HΦ $$ []
  itrivial

theorem deadlineSpec_isContext (parent : GoInterfaceOk) (s : ContextDesc (IProp GF)) :
    isContext parent s ⊢ deadlineSpec parent s.Deadline := by
  unfold isContext isContextDef deadlineSpec
  iintro ⟨#HDeadline, -⟩
  iexact HDeadline

/-- A `*cancelCtx` `c` (names `γ`, Done proposition `P`) whose parent has the deadline
`s.Deadline` is a context described by `s`. -/
theorem isContext_cancelCtx (c : Loc) (γ : ContextNames) (P : IProp GF) (parent : GoInterfaceOk)
    (s : ContextDesc (IProp GF)) (hγ : s.Done_gn = γ) (hP : s.PDone = P) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗
        ctxField c ↦□ (interface.ok parent : GoInterface) ∗ deadlineSpec parent s.Deadline ⊢
      isContext (interface.mk (go.GoType.PointerType context.cancelCtx.ty) #c) s := by
  iintro ⟨#Hpkg, #Hc, #Hf, #Hdl⟩
  unfold isContext isContextDef
  isplitl []
  · imodintro
    iintro %Φ - HΦ
    wp_method_call
    wp_auto
    unfold deadlineSpec
    iapply Hdl
    · itrivial
    iexact HΦ
  isplitl []
  · imodintro
    iintro %Φ - HΦ
    iapply wp_cancelCtx_Done $$ [$Hpkg $Hc]
    inext
    iintro %ch %γch ⟨#Hd, -⟩
    iapply HΦ
    iapply isContextDone_congr $$ Hd
    · unfold cdesc; simp [hγ]
    · unfold cdesc; simp [hP]
  isplitl []
  · iintro %cl
    imodintro
    iintro %Φ Hpre HΦ
    subst hγ hP
    dsimp only
    cases cl
    case Done =>
      iapply wp_cancelCtx_Err c _ _ true $$ [$Hpkg $Hc Hpre]
      · simp only [↓reduceIte]; iexact Hpre
      inext
      iintro %e ⟨%hne, -⟩
      iapply HΦ
      ipureintro; exact hne rfl
    all_goals
      iapply wp_cancelCtx_Err c _ _ false $$ [$Hpkg $Hc]
      · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      inext
      iintro %e ⟨-, He⟩
      iapply HΦ
      dsimp only
      by_cases he : e = interface.nil
      · subst he; simp only [ite_true]; itrivial
      · rw [ite_eq_right he]; rw [ite_eq_right he] at *
        icases He with ⟨-, #Hp, #Hcl⟩
        iframe #
  · imodintro
    iintro %Φ - HΦ
    iapply wp_cancelCtx_Value $$ [$Hpkg $Hc]
    inext
    iintro -
    iapply HΦ
    simp only [isCancelCtxAny, ↓reduceIte]
    iexists c
    isplitl []
    · ipureintro; rfl
    · unfold isCancelCtx; iexists γ, P; iexact Hc

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

/-- `WithCancel(parent)`, given the spec of `c.propagateCancel(parent, c)` (see `wp_withCancel`):
the new `*cancelCtx` and its cancel function. -/
theorem wp_WithCancel_gen (parent : GoInterfaceOk) (P Pre : IProp GF)
    (Hprop : ∀ (c : Loc) (γ : ContextNames),
      {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗
          ctxField c ↦ (interface.nil : GoInterface) ∗ Pre }}
        (App (App (Val (c @!! go.GoType.PointerType context.cancelCtx.ty @!! go!"propagateCancel"))
          (Val #(interface.ok parent)))
          (Val #(interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c)))
      {{ RET #(); ctxField c ↦ (interface.ok parent : GoInterface) }}) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ Pre ∗ isParentCtx parent }}
      (App (Val (@! context.WithCancel)) (Val #(interface.ok parent)))
    {{ (c : Loc) (γ : ContextNames) (cancel : GoFunc),
        RET (PairV #(interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c) #cancel);
        cancelSpec cancel γ P ∗ isCancelCtxOf c γ P ∗
        ctxField c ↦□ (interface.ok parent : GoInterface) }} := by
  wp_start as ⟨Hpre, #Hpar⟩
  ihave #Hi := isInit_access $$ Hpkg
  icases Hi with ⟨_, _, ⟨%canceled, #Hcanceled, %hcanceled⟩, _⟩
  wp_auto
  iapply wp_fupd
  wp_apply wp_withCancel parent P Pre Hprop $$ [$Hpre] as %c %γ ⟨#Hc, #Hf⟩
  ipersist c
  imodintro
  simp only [recv_eq_func_mk]
  iapply HΦ
  iframe #
  unfold cancelSpec
  imodintro
  iintro %Φ' #Hp HΦ'
  wp_auto
  wp_apply wp_cancelCtx_cancel c γ P true canceled GoInterface.nil hcanceled $$ [$Hc]
    as #Hclosed
  · iframe #
    simp only [↓reduceIte]
    iexists parent
    iframe #
  iapply HΦ' $$ Hclosed

/-- `WithCancel(ctx)` for a parent `ctx` that is a `*cancelCtx` made by `WithCancel`
(`isCancelCtxCtx`). The new context's Done channel does not exist yet when `WithCancel` returns,
so the postcondition gives fresh ghost names `γ'` for it. The cancel function's precondition is
`□ PDone'` (closing the Done channel needs the persistent Done proposition); it makes the new
context done (`ContextClosed γ'`). Observers of the new context's Done channel get
`□ (ctx_desc.PDone ∨ PDone')`: it is closed by the cancel function or when the parent is
canceled (the new context is in the parent's `children`). -/
theorem wp_WithCancel (PDone' : IProp GF) (ctx : GoInterfaceOk)
    (ctx_desc : ContextDesc (IProp GF)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isContext ctx ctx_desc ∗
        isCancelCtxCtx ctx ctx_desc }}
      (App (Val (@! context.WithCancel)) (Val #(interface.ok ctx)))
    {{ (ctx' : GoInterfaceOk) (γ' : ContextNames) (cancel : GoFunc),
        RET (PairV #(interface.ok ctx') #cancel);
        □ (∀ Φ : val → IProp GF, □ PDone' -∗ ▷ (ContextClosed γ' -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        isContext ctx' { ctx_desc with PDone := iprop(ctx_desc.PDone ∨ PDone'), Done_gn := γ' } ∗
        isCancelCtxCtx ctx'
          { ctx_desc with PDone := iprop(ctx_desc.PDone ∨ PDone'), Done_gn := γ' } }} := by
  iintro %Φ ⟨#Hpkg, #Hctx, #Hcc⟩ HΦ
  ihave #Hcc' := Hcc
  iunfold isCancelCtxCtx at Hcc'
  icases Hcc' with ⟨%p, %hp, -⟩
  iapply wp_WithCancel_gen ctx iprop(ctx_desc.PDone ∨ PDone')
      iprop(isContext ctx ctx_desc ∗ isCancelCtxCtx ctx ctx_desc ∗
        □ (ctx_desc.PDone -∗ iprop(ctx_desc.PDone ∨ PDone')))
      (fun c γ => wp_propagateCancel_cancelCtx c γ _ ctx ctx_desc)
  · iframe #
    isplitl []
    · imodintro; iintro H; ileft; iexact H
    unfold isParentCtx; iright; iexists ctx_desc; iframe #; ipureintro; rw [hp]
  inext
  iintro %c %γ %cancel ⟨#Hcancel, #Hc, #Hf⟩
  ihave #Hdl := deadlineSpec_isContext _ _ $$ Hctx
  iapply HΦ $$ %(interface.mk (go.GoType.PointerType context.cancelCtx.ty) #c)
  isplitl []
  · ihave #Hcancel' := cancelSpec_weaken cancel γ _ PDone' $$ [] Hcancel
    · imodintro; iintro H; iright; iexact H
    iunfold cancelSpec at Hcancel'
    iexact Hcancel'
  isplitl []
  · iapply isContext_cancelCtx c γ _ ctx _ rfl rfl
    iframe #
  · unfold isCancelCtxCtx; iexists c; iframe #; ipureintro; rfl

/-- `Background()` returns `backgroundCtxVal`. -/
theorem wp_Background :
    {{ (True : IProp GF) }}
      (App (Val (@! context.Background)) (Val #()))
    {{ RET #(interface.ok backgroundCtxVal); True }} := by
  wp_start
  iapply HΦ
  itrivial

/-- `WithCancel(Background())`: as `wp_WithCancel`, for a parent that is never done, with no
values and no deadline (so the new context's `PDone` is just `PDone'`, which the cancel function
needs). -/
theorem wp_WithCancel_Background (PDone' : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context }}
      (App (Val (@! context.WithCancel)) (Val #(interface.ok backgroundCtxVal)))
    {{ (ctx' : GoInterfaceOk) (γ' : ContextNames) (cancel : GoFunc),
        RET (PairV #(interface.ok ctx') #cancel);
        □ (∀ Φ : val → IProp GF, □ PDone' -∗ ▷ (ContextClosed γ' -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        isContext ctx' { Values := ∅, Deadline := none, Done_gn := γ', PDone := PDone' } ∗
        isCancelCtxCtx ctx' { Values := ∅, Deadline := none, Done_gn := γ', PDone := PDone' } }} := by
  iintro %Φ #Hpkg HΦ
  iapply wp_WithCancel_gen backgroundCtxVal PDone' iprop(True)
      (fun c γ => by
        iintro %Φ ⟨#Hpkg, -, Hf, -⟩ HΦ
        iapply wp_propagateCancel_background c $$ [$Hpkg $Hf] HΦ)
  · iframe #
    isplitl []
    · itrivial
    unfold isParentCtx; ileft; ipureintro; rfl
  inext
  iintro %c %γ %cancel ⟨#Hcancel, #Hc, #Hf⟩
  ihave #Hdl := deadlineSpec_background (GF := GF)
  iapply HΦ $$ %(interface.mk (go.GoType.PointerType context.cancelCtx.ty) #c)
  isplitl []
  · unfold cancelSpec; iexact Hcancel
  isplitl []
  · iapply isContext_cancelCtx c γ PDone' backgroundCtxVal _ rfl rfl
    iframe #
  · unfold isCancelCtxCtx; iexists c; iframe #; ipureintro; rfl

/-- Fresh ghost names `γ'` for the Done channel (see `wp_WithCancel`), and the deadline is
`some d'` with `d' = d ∨ parent_desc.Deadline = some d'`: `Deadline := some d` would be false
when the parent's deadline `cur` is before `d`, as `WithDeadlineCause` then returns `WithCancel(parent)`, whose `Deadline()` is
the parent's `cur`. -/
theorem wp_WithDeadlineCause (parent : GoInterfaceOk) (parent_desc : ContextDesc (IProp GF))
    (d : time.Time) (cause : GoError) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isContext parent parent_desc }}
      (App (App (App (Val (@! context.WithDeadlineCause)) (Val #(interface.ok parent))) (Val #d))
        (Val #cause))
    {{ (ctx' : GoInterfaceOk) (γ' : ContextNames) (cancel : GoFunc) (d' : time.Time),
        RET (PairV #(interface.ok ctx') #cancel);
        ⌜d' = d ∨ parent_desc.Deadline = some d'⌝ ∗
        □ (∀ Φ : val → IProp GF, True -∗ ▷ (True -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        isContext ctx'
          { parent_desc with Deadline := some d', PDone := iprop(True), Done_gn := γ' } }} := by
  -- Unprovable: it calls `cur.Before(d)` (`time.Time.Before`), `time.AfterFunc` and (in
  -- `timerCtx.cancel`) `c.timer.Stop()`, which are neither translated
  -- (`Perennial/Code/time.toml`) nor axiomatized. (Its `WithCancel(parent)` case and the
  -- `*cancelCtx` embedded in the `timerCtx` would also need `WithCancel` for an arbitrary
  -- `isContext` parent, see the file header.)
  sorry -- not proved

/-- Fresh ghost names and an existential deadline, as for `wp_WithDeadlineCause`. -/
theorem wp_WithDeadline (parent : GoInterfaceOk) (parent_desc : ContextDesc (IProp GF))
    (d : time.Time) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isContext parent parent_desc }}
      (App (App (Val (@! context.WithDeadline)) (Val #(interface.ok parent))) (Val #d))
    {{ (ctx' : GoInterfaceOk) (γ' : ContextNames) (cancel : GoFunc) (d' : time.Time),
        RET (PairV #(interface.ok ctx') #cancel);
        ⌜d' = d ∨ parent_desc.Deadline = some d'⌝ ∗
        □ (∀ Φ : val → IProp GF, True -∗ ▷ (True -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        isContext ctx'
          { parent_desc with Deadline := some d', PDone := iprop(True), Done_gn := γ' } }} := by
  wp_start as #Hctx
  wp_auto
  wp_apply wp_WithDeadlineCause $$ [$Hctx] as %ctx' %γ' %cancel %d' ⟨%hd, #Hcancel, #Hctx'⟩
  wp_end
  iframe #
  ipureintro; exact hd

/-- Fresh ghost names `γ'` for the Done channel (see `wp_WithCancel`). -/
theorem wp_WithTimeout (parent : GoInterfaceOk) (parent_desc : ContextDesc (IProp GF))
    (timeout : time.Duration) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isContext parent parent_desc }}
      (App (App (Val (@! context.WithTimeout)) (Val #(interface.ok parent))) (Val #(timeout)))
    {{ (ctx' : GoInterfaceOk) (γ' : ContextNames) (cancel : GoFunc) (d : time.Time),
        RET (PairV #(interface.ok ctx') #cancel);
        □ (∀ Φ : val → IProp GF, True -∗ ▷ (True -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        isContext ctx'
          { parent_desc with Deadline := some d, PDone := iprop(True), Done_gn := γ' } }} := by
  wp_start as #Hctx
  wp_auto
  wp_apply time.wp_Now as %now -
  wp_apply time.Time.wp_Add as %d -
  wp_apply wp_WithDeadline $$ [$Hctx] as %ctx' %γ' %cancel %d' ⟨-, #Hcancel, #Hctx'⟩
  wp_end
  iframe #

end wps

end context

end Perennial
end
