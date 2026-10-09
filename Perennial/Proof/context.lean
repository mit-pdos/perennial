/-
Specifications for Go's `context` package.

Proved: `wp_Cause`, `wp_parentCancelCtx`, `wp_Background`, and `wp_WithDeadline` /
`wp_WithTimeout` (from the specs of `WithDeadlineCause` / `WithDeadline`). `wp_WithCancel`,
`wp_WithCancel_Background` (`WithCancel(Background())`: `Background()` is not an `isContext`),
`wp_WithDeadlineCause` and `wp_propagateCancel` are `sorry` (see the comments in their proofs: `atomic.Value` is
unspecifiable in the model, and `time.Time.Before`, `time.AfterFunc`, `Timer.Stop` have no
model). There is no spec for the internal `withCancel`.

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
  - `isContextDone s ch γch` (persistent): `ch` is the Done channel; the done cell holds
    `ch`, and `ch` is a broadcast channel, with an existential proposition `Q` implying
    `□ s.PDone ∗ ContextClosed s.Done_gn`. Client lemmas: `isContextDone_is_chan`,
    `isContextDone_receive` (`recvAu`, e.g. for a `select` case),
    `isContextDone_nonblocking_receive`, `isContextDone_agree` (successive `Done()` calls
    return the same channel), `isContextDone_weaken`.
  - `isContext`: `"#HDone"` returns some `ch` with `isContextDone s ch γch`; `"#HErr"` takes
    `ContextClosed s.Done_gn` for `cl = Done` (nothing otherwise) and returns
    `□ s.PDone ∗ ContextClosed s.Done_gn` for a non-nil error.
  - `isContext_weaken`: `isContext` is monotone in `PDone`.
  - `wp_WithCancel`, `wp_WithDeadlineCause`, `wp_WithDeadline`, `wp_WithTimeout` return
    fresh ghost names `γ' : ContextNames` for the new context (`Done_gn := γ'`).
* `wp_WithCancel`: the cancel function's precondition is `□ PDone'` (closing the broadcast
  channel needs `□ PDone`).
* `wp_WithDeadlineCause`, `wp_WithDeadline`: the deadline is an existential `some d'` with
  `d' = d ∨ parent_desc.Deadline = some d'`, since when the parent's deadline is earlier,
  `WithDeadlineCause` returns `WithCancel(parent)`.
* `isInit` includes `"#Hclosedchan"`: the global `closedchan` holds a fixed channel (Go never
  writes it after initialization). Needed by `parentCancelCtx`, which compares
  `parent.Done()` with `closedchan`.
* `isContext` includes `"#HValue"`, the spec of `c.Value(&cancelCtxKey)`: the result, if it
  is a `*cancelCtx`, is a valid one (`isCancelCtx`). `Cause`, `parentCancelCtx` (and through
  it `propagateCancel`, `removeChild`) call `Value(&cancelCtxKey)` to find the innermost
  `*cancelCtx`.
* Helper definitions: `cancelCtxKeyAny`, `cancelCtxLockInv`, `isCancelCtx`,
  `isCancelCtxAny`, `isInit_access`, `broadcast_chan_nonblocking_receive_Q`.
* `wp_parentCancelCtx`: the postcondition in the `ok` case is `isCancelCtx ctx`.

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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- The package invariant: the `goroutines` counter, and `"#Hclosedchan"`: the global
`closedchan` holds a fixed channel. -/
abbrev isInit : IProp GF :=
  iprop("Hgoroutines" ∷
    inv nroot (∃ g, sync.atomic.ownInt32 (globalAddr context.goroutines) (DFrac.own 1) g) ∗
  "#Hclosedchan" ∷ (∃ ch : GoChan, globalAddr context.closedchan ↦□ ch) ∗
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
def cancelCtxKeyAny [GoSemanticsFunctions] : GoInterface :=
  interface.mkOk (go.GoType.PointerType go.int) #(globalAddr context.cancelCtxKey)

/-- Lock invariant of `c.mu` for a `*cancelCtx` `c`: the fields that the Go
code only accesses with `c.mu` held (`children` and `cause`; `done` and `err`
are `atomic.Value`s, also read without the lock). -/
def cancelCtxLockInv (c : Loc) : IProp GF :=
  iprop(∃ (children : GoMap) (cause : GoError),
    "children" ∷ structFieldRef context.cancelCtx go!"children" c ↦ children ∗
    "cause" ∷ structFieldRef context.cancelCtx go!"cause" c ↦ cause)

/-- `c` is a (shared) `*cancelCtx`. `atomic.Value` is implemented with
`unsafe.Pointer` conversions that the model cannot verify, so the spec of
`c.done.Load()` (it holds `nil` or a `chan struct{}`) is part of the
predicate. -/
def isCancelCtx (c : Loc) : IProp GF :=
  iprop(
  "#Hmu" ∷ sync.isMutex (structFieldRef context.cancelCtx go!"mu" c) (cancelCtxLockInv c) ∗
  "#Hdone_Load" ∷
    □ (∀ Φ : val → IProp GF, True -∗
      ▷ (∀ ch : Option GoChan,
          Φ #(match ch with
              | none => interface.nil
              | some ch => interface.mkOk
                  (go.GoType.ChannelType go.ChanDir.sendrecv (go.GoType.StructType [])) #ch)) -∗
      WP (App (Val (structFieldRef context.cancelCtx go!"done" c @!!
        go.GoType.PointerType sync.atomic.Value.ty @!! go!"Load")) (Val #())) {{ Φ }}))

instance isCancelCtx_pers (c : Loc) : Persistent (isCancelCtx (GF := GF) c) := by
  unfold isCancelCtx; infer_instance

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

/-- The context with ghost names `γ` is done (canceled or past its deadline). Persistent. -/
def ContextClosed (γ : ContextNames) : IProp GF :=
  dghostVar γ.closedGn .discard true

instance contextClosed_pers (γ : ContextNames) : Persistent (ContextClosed (GF := GF) γ) := by
  unfold ContextClosed; infer_instance

/-- `ch` (with channel names `γch`) is the Done channel of the context `s`: the context's
done cell holds `ch`, and `ch` is a broadcast channel whose closing implies that `s` is done
(`ContextClosed`) and `□ s.PDone`. Persistent.

The broadcast proposition `Q` is existential: a `*cancelCtx` whose channel is made by
`Done()` uses `Q := s.PDone ∗ ContextClosed s.Done_gn`, while one whose `cancel` ran first
returns the shared, already closed `closedchan` (whose broadcast proposition is fixed at
package initialization), with `□ s.PDone ∗ ContextClosed s.Done_gn` known when the done cell
is set. -/
def isContextDoneDef (s : ContextDesc (IProp GF)) (ch : GoChan) (γch : ChanNames) :
    IProp GF :=
  iprop(dghostVar s.Done_gn.doneGn .discard (some ch) ∗
    ∃ Q : IProp GF, ownBroadcastChan ch γch Q .Unknown ∗
      □ (□ Q -∗ □ s.PDone ∗ ContextClosed s.Done_gn))
@[irreducible] def isContextDone (s : ContextDesc (IProp GF)) (ch : GoChan)
    (γch : ChanNames) : IProp GF := isContextDoneDef s ch γch
theorem isContextDone_unseal : @isContextDone = @isContextDoneDef := by
  funext; with_unfolding_all rfl

instance isContextDone_pers (s : ContextDesc (IProp GF)) (ch : GoChan) (γch : ChanNames) :
    Persistent (isContextDone s ch γch) := by
  rw [isContextDone_unseal]; unfold isContextDoneDef; infer_instance

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
  iintro ⟨-, %Q, #Hbc, -⟩
  iapply ownBroadcastChan_is_chan $$ Hbc

/-- Successive `Done()` calls return the same channel. -/
theorem isContextDone_agree (s : ContextDesc (IProp GF)) (ch1 ch2 : GoChan)
    (γ1 γ2 : ChanNames) :
    isContextDone s ch1 γ1 ∗ isContextDone s ch2 γ2 ⊢ ⌜ch1 = ch2⌝ := by
  rw [isContextDone_unseal]; unfold isContextDoneDef
  iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
  ihave %h := dghostVar_agree _ _ _ _ _ $$ H1 H2
  ipureintro; exact Option.some.inj h

/-- Receiving from the Done channel (e.g. as a `select` case) returns only once the context is
done. -/
theorem isContextDone_receive (s : ContextDesc (IProp GF)) (ch : GoChan) (γch : ChanNames)
    (Φ : Unit → Bool → IProp GF) :
    ⊢ isContextDone s ch γch -∗
      (□ s.PDone ∗ ContextClosed s.Done_gn -∗ Φ () false) -∗
      recvAu γch Unit Φ := by
  rw [isContextDone_unseal]; unfold isContextDoneDef
  iintro ⟨-, %Q, #Hbc, #HQ⟩ HΦ
  iapply broadcast_chan_receive _ _ _ _ _ $$ Hbc
  iintro ⟨#Hq, -⟩
  iapply HΦ
  iapply HQ $$ Hq

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
  iintro ⟨-, %Q, #Hbc, #HQ⟩ HΦ
  iapply broadcast_chan_nonblocking_receive_Q _ _ _ _ _ $$ Hbc
  isplit
  · iintro #Hq
    icases HΦ with ⟨HΦ, -⟩
    iapply HΦ
    iapply HQ $$ Hq
  · icases HΦ with ⟨-, HΦ⟩
    iexact HΦ

/-- The Done proposition can be weakened. -/
theorem isContextDone_weaken (s : ContextDesc (IProp GF)) (P' : IProp GF) (ch : GoChan)
    (γch : ChanNames) :
    ⊢ □ (s.PDone -∗ P') -∗ isContextDone s ch γch -∗
      isContextDone { s with PDone := P' } ch γch := by
  rw [isContextDone_unseal]; unfold isContextDoneDef
  iintro #HP ⟨#Hd, %Q, #Hbc, #HQ⟩
  isplitl []
  · iexact Hd
  iexists Q
  isplitl []
  · iexact Hbc
  imodintro
  iintro #Hq
  icases HQ $$ Hq with ⟨#Hp, #Hc⟩
  isplitl []
  · imodintro; iapply HP $$ Hp
  · iexact Hc

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
        icases Hcc with ⟨#Hmu, #Hdone_Load⟩
        wp_auto
        wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
        unfold cancelCtxLockInv
        icases Hinv with ⟨%children, %cause, Hchildren, Hcause⟩
        wp_auto
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hchildren Hcause]
        · inext; iexists _, _; iframe
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
  icases Hi with ⟨_, ⟨%closed, #Hclosed⟩, _⟩
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
      icases Hc' with ⟨#Hmu, #Hdone_Load⟩
      wp_apply Hdone_Load as %och
      cases och with
      | none =>
        wp_auto
        have h3 : decide (zero_val GoChan = done) = false := by
          simp only [decide_eq_false_iff_not]; exact fun h => h2 h.symm
        simp only [h3]
        wp_auto
        wp_end
        simp only [Bool.false_eq_true, ↓reduceIte]
        ipureintro; trivial
      | some ch =>
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

theorem wp_propagateCancel (c : Loc) (parent : GoInterfaceOk)
    (parent_desc : ContextDesc (IProp GF)) (child : GoInterfaceOk) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗
        "Hparent" ∷ isContext parent parent_desc ∗
        "Hc" ∷ c ↦ (zero_val context.cancelCtx) }}
      (App (App (Val (c @!! go.GoType.PointerType context.cancelCtx.ty @!! go!"propagateCancel"))
        (Val #(interface.ok parent))) (Val #(interface.ok child)))
    {{ RET #(); True }} := by
  -- Still unprovable as stated (with `#HValue` the `parentCancelCtx` call is now covered):
  -- * `child.cancel(..)` and `child.Done()` are called, but the precondition says nothing
  --   about `child` (it would need a canceler spec for `child`);
  -- * `p.err.Load()` on the parent's `*cancelCtx` (`atomic.Value`, implemented with
  --   `unsafe.Pointer`; `isCancelCtx` would need its spec, typing the stored value as an
  --   `error`), and the `p.children` map with `canceler` interface keys;
  -- * `parent.(afterFuncer)`: a parent with an `AfterFunc` method needs a spec for it;
  -- * the forked goroutine selects on `parent.Done()` and `child.Done()`.
  sorry -- not proved

/-- The new context's Done channel does not exist yet when `WithCancel` returns, so the
postcondition gives fresh ghost names `γ'` for it; the cancel function's precondition is
`□ PDone'` (closing a broadcast channel needs the persistent `□ PDone`, and observers of the Done channel get
`□ (ctx_desc.PDone ∨ PDone')`). -/
theorem wp_WithCancel (PDone' : IProp GF) (ctx : GoInterfaceOk)
    (ctx_desc : ContextDesc (IProp GF)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isContext ctx ctx_desc }}
      (App (Val (@! context.WithCancel)) (Val #(interface.ok ctx)))
    {{ (ctx' : GoInterfaceOk) (γ' : ContextNames) (cancel : GoFunc),
        RET (PairV #(interface.ok ctx') #cancel);
        □ (∀ Φ : val → IProp GF, □ PDone' -∗ ▷ (True -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        isContext ctx' { ctx_desc with PDone := iprop(ctx_desc.PDone ∨ PDone'), Done_gn := γ' } }} := by
  -- Unprovable: `WithCancel` builds a `*cancelCtx`, whose `Done`, `Err` and `cancel` methods
  -- (and `withCancel`'s call of `propagateCancel`) use the `atomic.Value` fields `done` and
  -- `err`. `atomic.Value`'s methods are translated Go code that reinterprets the `any` field
  -- `v` of a `Value` as an `efaceWords` struct of two `unsafe.Pointer`s (`Load`: `vp :=
  -- (*efaceWords)(unsafe.Pointer(v)); LoadPointer(&vp.typ)`, likewise `Store`/`Swap`/
  -- `CompareAndSwap`, which also use `runtime_procPin`). The model has no such layout law:
  -- `structFieldRef efaceWords.t "typ" l` is unrelated to `structFieldRef Value.t "v" l`,
  -- and an `GoInterface` value is not a pair of words, so no spec of `Value.Load`/`Store` is
  -- provable from `l ↦ (v : Value.t)` (the loads hit unowned memory). With trusted models of
  -- `atomic.Value`'s methods (as for `sync.Mutex`), the remaining proof obligations are:
  -- * `withCancel`/`propagateCancel`: a `*cancelCtx` invariant (lock invariant of `c.mu` with
  --   `children`, each child with its stored `cancel` spec, and `cause`; an `inv` for the
  --   `done`/`err` cells, the done cell `ContextNames.doneGn` and the closed flag), the
  --   `parentCancelCtx` branch (`p.err.Load()`, `p.children` map with `canceler` keys; it
  --   needs `isCancelCtxAny` to relate the found `p`'s names and `PDone` to the parent's
  --   when `p.done.Load() == parent.Done()`), the `parent.(afterFuncer)` branch (a spec for
  --   the parent's `AfterFunc`, or the knowledge that its type has none), and the goroutine
  --   branch (`select` on `parent.Done()` / `child.Done()`);
  -- * the cancel closure: `c.cancel(true, Canceled, nil)`, including `removeChild` and the
  --   iteration over `c.children` (map `range` with interface keys);
  -- * `is_init` must additionally provide the `Canceled` global (a non-nil `error`) and the
  --   broadcast state of `closedchan` (closed, with `Q := True`).
  sorry -- not proved

/-- The context `Background()` returns: a `backgroundCtx{}` as a `Context`. Its `Done()` is
`nil` (it is never canceled), so it is not an `isContext`; `wp_WithCancel_Background` derives a
cancelable context from it. -/
abbrev backgroundCtxVal : GoInterfaceOk :=
  interface.mk backgroundCtx.ty #(zero_val backgroundCtx)

/-- `Background()` returns `backgroundCtxVal`. -/
theorem wp_Background :
    {{ (True : IProp GF) }}
      (App (Val (@! context.Background)) (Val #()))
    {{ RET #(interface.ok backgroundCtxVal); True }} := by
  wp_start
  iapply HΦ
  itrivial

/-- `WithCancel(Background())`: as `wp_WithCancel` for a parent that is never done, with no
values and no deadline (so the new context's `PDone` is just `PDone'`, which the cancel function
needs). -/
theorem wp_WithCancel_Background (PDone' : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context }}
      (App (Val (@! context.WithCancel)) (Val #(interface.ok backgroundCtxVal)))
    {{ (ctx' : GoInterfaceOk) (γ' : ContextNames) (cancel : GoFunc),
        RET (PairV #(interface.ok ctx') #cancel);
        □ (∀ Φ : val → IProp GF, □ PDone' -∗ ▷ (True -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        isContext ctx' { Values := ∅, Deadline := none, Done_gn := γ', PDone := PDone' } }} := by
  -- Unprovable for the same reason as `wp_WithCancel` (the `*cancelCtx`'s `atomic.Value`
  -- fields); `propagateCancel` returns at once for this parent (its `Done()` is `nil`).
  sorry -- not proved

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
  -- Unprovable: besides the `*cancelCtx` gaps of `wp_WithCancel` (`atomic.Value`), it calls
  -- `cur.Before(d)` (`time.Time.Before`), `time.AfterFunc` and (in `timerCtx.cancel`)
  -- `c.timer.Stop()`, which are neither translated (`Perennial/Code/time.toml`) nor
  -- axiomatized.
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
