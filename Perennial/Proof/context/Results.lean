/-
Results of `context` derived from the linked ones, under their old names: the methods of
`*cancelCtx` and `*timerCtx` (`wp_cancelCtx_Done`, ..., `wp_timerCtx_cancel`, the Link's
`cancelCtx.wp_Done`, ...), the promoted methods of `*timerCtx` (`wp_timerCtx_Done`, ...), the
three cases of `propagateCancel`'s spec (`wp_propagateCancel_background`, `_background_any`,
`_cancelCtx`, `_any`), the other triples of `WithCancel` (`wp_WithCancel_gen`, `wp_WithCancel_any`,
`wp_WithCancel_Background`), of the deadline constructors (`wp_WithDeadlineCause_Background`,
`wp_WithDeadline_Background`, `wp_WithTimeout_Background`) and of `parentCancelCtx` (`wp_parentCancelCtx_self`,
`wp_parentCancelCtx_timer`), the `atomic.Value` cells (`wp_done_Load`, ...) and the `isContext`s of
`*cancelCtx` and `*timerCtx`: each the shared `_of` lemma applied to the linked results.
-/
module

public import Perennial.Proof.context.Link
public import Perennial.Proof.context.CancelCtxCells
public import Perennial.Proof.context.CancelCtxContext
public import Perennial.Proof.context.TimerCtx
public import Perennial.Proof.context.PropagateCancel
public import Perennial.Proof.context.WithCancelGen
public import Perennial.Proof.context.WithDeadlineBackground

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace context

section results
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

open ContextDesc

/-- `cancelCtx.wp_Done` under its old name. -/
theorem wp_cancelCtx_Done : cancelCtx.Done.spec (GF := GF) (hG := hG) :=
  cancelCtx.wp_Done

/-- `cancelCtx.wp_Err` under its old name. -/
theorem wp_cancelCtx_Err : cancelCtx.Err.spec (GF := GF) (hG := hG) :=
  cancelCtx.wp_Err

/-- `cancelCtx.wp_Value` under its old name. -/
theorem wp_cancelCtx_Value : cancelCtx.Value.spec (GF := GF) (hG := hG) :=
  cancelCtx.wp_Value

/-- `cancelCtx.wp_cancel` under its old name. -/
theorem wp_cancelCtx_cancel : cancelCtx.cancel.spec (GF := GF) (hG := hG) :=
  cancelCtx.wp_cancel

/-- `timerCtx.wp_cancel` under its old name. -/
theorem wp_timerCtx_cancel : timerCtx.cancel.spec (GF := GF) (hG := hG) :=
  timerCtx.wp_cancel

/-- `c.done.Load()` without the lock: `nil`, or a determined Done channel. -/
theorem wp_done_Load (c : Loc) (γ : ContextNames) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P }}
      (App (Val (structFieldRef context.cancelCtx go!"done" c @!!
        go.GoType.PointerType sync.atomic.Value.ty @!! go!"Load")) (Val #()))
    {{ (od : Option GoChan), RET #(doneAny od);
        match od with
        | none => iprop(True)
        | some ch => ∃ γch, isContextDone (cdesc γ P) ch γch ∗ doneFresh γ P ch }} :=
  wp_done_Load_of sync.atomic.Value.wp_Load c γ P

/-- `c.done.Load()` given the lock invariant's half of the done cell, which determines the
result. -/
theorem wp_done_Load_frag (c : Loc) (γ : ContextNames) (P : IProp GF) (od : Option GoChan) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗ doneFrag γ od }}
      (App (Val (structFieldRef context.cancelCtx go!"done" c @!!
        go.GoType.PointerType sync.atomic.Value.ty @!! go!"Load")) (Val #()))
    {{ RET #(doneAny od); doneFrag γ od ∗
        match od with
        | none => iprop(True)
        | some ch => ∃ γch, isContextDone (cdesc γ P) ch γch ∗ doneFresh γ P ch }} :=
  wp_done_Load_frag_of sync.atomic.Value.wp_Load c γ P od

/-- `c.err.Load()` without the lock; given `ContextClosed γ` (`cl`), the error is not `nil`. -/
theorem wp_err_Load (c : Loc) (γ : ContextNames) (P : IProp GF) (cl : Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗
        (if cl then ContextClosed γ else iprop(True)) }}
      (App (Val (structFieldRef context.cancelCtx go!"err" c @!!
        go.GoType.PointerType sync.atomic.Value.ty @!! go!"Load")) (Val #()))
    {{ (e : GoInterface), RET #e; ⌜cl = true → e ≠ interface.nil⌝ ∗
        (if e = interface.nil then iprop(True)
         else iprop(⌜isTypedErr e⌝ ∗ □ P ∗ ContextClosed γ)) }} :=
  wp_err_Load_of sync.atomic.Value.wp_Load c γ P cl

/-- `c.err.Load()` given the lock invariant's half of the closed flag, which determines whether
the result is `nil`. -/
theorem wp_err_Load_frag (c : Loc) (γ : ContextNames) (P : IProp GF) (closed : Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗ closedFrag γ closed }}
      (App (Val (structFieldRef context.cancelCtx go!"err" c @!!
        go.GoType.PointerType sync.atomic.Value.ty @!! go!"Load")) (Val #()))
    {{ (e : GoInterface), RET #e; closedFrag γ closed ∗
        ⌜closed = false → e = interface.nil⌝ ∗ ⌜closed = true → isTypedErr e⌝ ∗
        □ (⌜closed = true⌝ -∗ P) }} :=
  wp_err_Load_frag_of sync.atomic.Value.wp_Load c γ P closed

/-- `c.done.Load()` once the Done channel `ch` is known: it returns `ch`. -/
theorem wp_done_Load_known (c : Loc) (γ : ContextNames) (P : IProp GF) (ch : GoChan) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗
        dghostVar γ.doneGn .discard (some ch) }}
      (App (Val (structFieldRef context.cancelCtx go!"done" c @!!
        go.GoType.PointerType sync.atomic.Value.ty @!! go!"Load")) (Val #()))
    {{ RET #(doneAny (some ch)); True }} :=
  wp_done_Load_known_of sync.atomic.Value.wp_Load c γ P ch

/-- `parentCancelCtx(p)` for a `*cancelCtx` `p` whose Done channel `ch` (once determined, e.g.
by an earlier `p.Done()`) is not `closedchan`: it returns `p`. -/
theorem wp_parentCancelCtx_self (p : Loc) (γ : ContextNames) (P : IProp GF) (ch cch : GoChan)
    (hcch : ch ≠ cch) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf p γ P ∗
        dghostVar γ.doneGn .discard (some ch) ∗ globalAddr context.closedchan ↦□ cch }}
      (App (Val (@! context.parentCancelCtx))
        (Val #(interface.ok (interface.mk (go.GoType.PointerType context.cancelCtx.ty) #p))))
    {{ RET (PairV #p #true); True }} :=
  wp_parentCancelCtx_self_of cancelCtx.wp_Done cancelCtx.wp_Value sync.atomic.Value.wp_Load p γ P ch
    cch hcch

/-- The `childCancelSpec` of a `*cancelCtx` child whose Done proposition follows from the
parent's. -/
theorem childCancelSpec_cancelCtx (c : Loc) (γ : ContextNames) (P Q : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗ □ (Q -∗ P) ⊢
      childCancelSpec Q (interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c) :=
  childCancelSpec_cancelCtx_of cancelCtx.wp_cancel c γ P Q

/-- A `*cancelCtx` `c` (names `γ`, Done proposition `P`) whose parent has the deadline
`s.Deadline` is a context described by `s`. -/
theorem isContext_cancelCtx (c : Loc) (γ : ContextNames) (P : IProp GF) (parent : GoInterfaceOk)
    (s : ContextDesc (IProp GF)) (hγ : s.Done_gn = γ) (hP : s.PDone = P) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗
        ctxField c ↦□ (interface.ok parent : GoInterface) ∗ deadlineSpec parent s.Deadline ⊢
      isContext (interface.mk (go.GoType.PointerType context.cancelCtx.ty) #c) s :=
  isContext_cancelCtx_of cancelCtx.wp_Done cancelCtx.wp_Err cancelCtx.wp_Value
    sync.atomic.Value.wp_Load c γ P parent s hγ hP

/-- `c.propagateCancel(Background(), c)`: the parent is never canceled (`Done()` is `nil`). -/
theorem wp_propagateCancel_background (c : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗
        ctxField c ↦ (interface.nil : GoInterface) }}
      (App (App (Val (c @!! go.GoType.PointerType context.cancelCtx.ty @!! go!"propagateCancel"))
        (Val #(interface.ok backgroundCtxVal)))
        (Val #(interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c)))
    {{ RET #(); ctxField c ↦ (interface.ok backgroundCtxVal : GoInterface) }} :=
  wp_propagateCancel_background_of cancelCtx.wp_propagateCancel c

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
    {{ RET #(); ctxField c ↦ (interface.ok parent : GoInterface) }} :=
  wp_propagateCancel_cancelCtx_of cancelCtx.wp_propagateCancel c γ P parent s

/-- `c.propagateCancel(parent, child)` for any context `parent` (`isContext`) and a child whose
`cancel(false, err, cause)` needs nothing but a typed error (`childCancelSpec True`): the child
is canceled at once if the parent is done, and is otherwise added to the `children` of the
`*cancelCtx` that `parentCancelCtx(parent)` finds (`"#HParentCC"`; the branches for other
parents are not reached). -/
theorem wp_propagateCancel_any (c : Loc) (parent : GoInterfaceOk) (s : ContextDesc (IProp GF))
    (k : GoInterface) [SafeMapKey (GF := GF) context.canceler.ty k] :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗
        ctxField c ↦ (interface.nil : GoInterface) ∗ isContext parent s ∗
        childCancelSpec iprop(True) k }}
      (App (App (Val (c @!! go.GoType.PointerType context.cancelCtx.ty @!! go!"propagateCancel"))
        (Val #(interface.ok parent)))
        (Val #k))
    {{ RET #(); ctxField c ↦ (interface.ok parent : GoInterface) }} :=
  wp_propagateCancel_any_of cancelCtx.wp_propagateCancel c parent s k

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
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isClosedchanInit ∗ Pre ∗
        isParentCtx parent }}
      (App (Val (@! context.WithCancel)) (Val #(interface.ok parent)))
    {{ (c : Loc) (γ : ContextNames) (cancel : GoFunc),
        RET (PairV #(interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c) #cancel);
        cancelSpec cancel γ P ∗ isCancelCtxOf c γ P ∗
        ctxField c ↦□ (interface.ok parent : GoInterface) }} :=
  wp_WithCancel_gen_of wp_withCancel cancelCtx.wp_cancel parent P Pre Hprop

/-- `WithCancel(parent)` for any context `parent` (`isContext`): the new context is a
`*cancelCtx` with the parent's deadline whose cancel function needs nothing (so its Done
proposition is `True`). -/
theorem wp_WithCancel_any (parent : GoInterfaceOk) (s : ContextDesc (IProp GF)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isContext parent s }}
      (App (Val (@! context.WithCancel)) (Val #(interface.ok parent)))
    {{ (ctx' : GoInterfaceOk) (γ' : ContextNames) (cancel : GoFunc),
        RET (PairV #(interface.ok ctx') #cancel);
        cancelSpec cancel γ' iprop(True) ∗
        isContext ctx' { s with PDone := iprop(True), Done_gn := γ' } }} :=
  wp_WithCancel_any_of wp_withCancel cancelCtx.wp_cancel cancelCtx.wp_propagateCancel
    cancelCtx.wp_Done cancelCtx.wp_Err cancelCtx.wp_Value sync.atomic.Value.wp_Load parent s

/-- `WithCancel(Background())`: as `wp_WithCancel`, for a parent that is never done, with no
values and no deadline (so the new context's `PDone` is just `PDone'`, which the cancel function
needs). -/
theorem wp_WithCancel_Background (PDone' : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isClosedchanInit }}
      (App (Val (@! context.WithCancel)) (Val #(interface.ok backgroundCtxVal)))
    {{ (ctx' : GoInterfaceOk) (γ' : ContextNames) (cancel : GoFunc),
        RET (PairV #(interface.ok ctx') #cancel);
        □ (∀ Φ : val → IProp GF, □ PDone' -∗ ▷ (ContextClosed γ' -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        isContext ctx' { Values := ∅, Deadline := none, Done_gn := γ', PDone := PDone' } ∗
        isCancelCtxCtx ctx' { Values := ∅, Deadline := none, Done_gn := γ', PDone := PDone' } }} :=
  wp_WithCancel_Background_of wp_withCancel cancelCtx.wp_cancel cancelCtx.wp_propagateCancel
    cancelCtx.wp_Done cancelCtx.wp_Err cancelCtx.wp_Value sync.atomic.Value.wp_Load PDone'

/-- `wp_timerCtx_Done_of` applied to the linked results (see there). -/
theorem wp_timerCtx_Done (c : Loc) (γ : ContextNames) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf (tcc c) γ P }}
      (App (Val #(methods (go.GoType.PointerType context.timerCtx.ty) go!"Done" #c)) (Val #()))
    {{ (ch : GoChan) (γch : ChanNames), RET #ch; isContextDone (cdesc γ P) ch γch ∗
        doneFresh γ P ch }} :=
  wp_timerCtx_Done_of cancelCtx.wp_Done c γ P

/-- `wp_timerCtx_Err_of` applied to the linked results (see there). -/
theorem wp_timerCtx_Err (c : Loc) (γ : ContextNames) (P : IProp GF) (cl : Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf (tcc c) γ P ∗
        (if cl then ContextClosed γ else iprop(True)) }}
      (App (Val #(methods (go.GoType.PointerType context.timerCtx.ty) go!"Err" #c)) (Val #()))
    {{ (e : GoInterface), RET #e; ⌜cl = true → e ≠ interface.nil⌝ ∗
        (if e = interface.nil then iprop(True)
         else iprop(⌜isTypedErr e⌝ ∗ □ P ∗ ContextClosed γ)) }} :=
  wp_timerCtx_Err_of cancelCtx.wp_Err c γ P cl

/-- `wp_timerCtx_Value_of` applied to the linked results (see there). -/
theorem wp_timerCtx_Value (c : Loc) (γ : ContextNames) (P : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf (tcc c) γ P }}
      (App (Val #(methods (go.GoType.PointerType context.timerCtx.ty) go!"Value" #c))
        (Val #cancelCtxKeyAny))
    {{ RET #(interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #(tcc c)); True }} :=
  wp_timerCtx_Value_of cancelCtx.wp_Value c γ P

/-- The `childCancelSpec` of a `*timerCtx` (it needs nothing of its parent's Done
proposition). -/
theorem childCancelSpec_timerCtx (c : Loc) (γ : ContextNames) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗
        isCancelCtxOfR (tcc c) γ iprop(True) (timerR c) ⊢
      childCancelSpec iprop(True)
        (interface.mkOk (go.GoType.PointerType context.timerCtx.ty) #c) :=
  childCancelSpec_timerCtx_of timerCtx.wp_cancel c γ

/-- `parentCancelCtx(c)` for a `*timerCtx` `c` whose Done channel `ch` is not `closedchan`: it
returns the embedded `*cancelCtx`. -/
theorem wp_parentCancelCtx_timer (c : Loc) (γ : ContextNames) (P : IProp GF) (ch cch : GoChan)
    (hcch : ch ≠ cch) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf (tcc c) γ P ∗
        dghostVar γ.doneGn .discard (some ch) ∗ globalAddr context.closedchan ↦□ cch }}
      (App (Val (@! context.parentCancelCtx))
        (Val #(interface.ok (interface.mk (go.GoType.PointerType context.timerCtx.ty) #c))))
    {{ RET (PairV #(tcc c) #true); True }} :=
  wp_parentCancelCtx_timer_of cancelCtx.wp_Done cancelCtx.wp_Value sync.atomic.Value.wp_Load c γ P
    ch cch hcch

/-- A `*timerCtx` `c` (names `γ`, Done proposition `True`) with deadline `d` is a context
described by `s` (whose deadline is `some d`). -/
theorem isContext_timerCtx (c : Loc) (γ : ContextNames) (d : time.Time)
    (s : ContextDesc (IProp GF)) (hγ : s.Done_gn = γ) (hP : s.PDone = iprop(True))
    (hd : s.Deadline = some d) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗
        isCancelCtxOfR (tcc c) γ iprop(True) (timerR c) ∗
        structFieldRef context.timerCtx go!"deadline" c ↦□ d ⊢
      isContext (interface.mk (go.GoType.PointerType context.timerCtx.ty) #c) s :=
  isContext_timerCtx_of cancelCtx.wp_Done cancelCtx.wp_Err cancelCtx.wp_Value
    sync.atomic.Value.wp_Load c γ d s hγ hP hd


/-- `wp_propagateCancel_background_any_of` applied to the linked results (see there). -/
theorem wp_propagateCancel_background_any (c : Loc) (k : GoInterface)
    [SafeMapKey (GF := GF) context.canceler.ty k] :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗
        ctxField c ↦ (interface.nil : GoInterface) }}
      (App (App (Val (c @!! go.GoType.PointerType context.cancelCtx.ty @!! go!"propagateCancel"))
        (Val #(interface.ok backgroundCtxVal)))
        (Val #k))
    {{ RET #(); ctxField c ↦ (interface.ok backgroundCtxVal : GoInterface) }} :=
  wp_propagateCancel_background_any_of cancelCtx.wp_propagateCancel c k

/-- `WithDeadlineCause(Background(), d, cause)` (`wp_WithDeadlineCause_Background_of` applied to
the linked results): a context with no values, the deadline `d` and the Done proposition `True`,
whose `cancel` needs nothing. -/
theorem wp_WithDeadlineCause_Background (d : time.Time) (cause : GoError) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context }}
      (App (App (App (Val (@! context.WithDeadlineCause)) (Val #(interface.ok backgroundCtxVal)))
        (Val #d)) (Val #cause))
    {{ (ctx' : GoInterfaceOk) (γ' : ContextNames) (cancel : GoFunc),
        RET (PairV #(interface.ok ctx') #cancel);
        □ (∀ Φ : val → IProp GF, True -∗ ▷ (True -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        isContext ctx' (bgDeadlineDesc d γ') }} :=
  wp_WithDeadlineCause_Background_of sync.Mutex.wp_Lock sync.Mutex.wp_Unlock
    sync.atomic.Value.wp_Load time.wp_Until time.wp_AfterFunc cancelCtx.wp_Done cancelCtx.wp_Err
    cancelCtx.wp_Value cancelCtx.wp_propagateCancel timerCtx.wp_cancel d cause

/-- `WithDeadline(Background(), d)` (see `wp_WithDeadlineCause_Background`). -/
theorem wp_WithDeadline_Background (d : time.Time) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context }}
      (App (App (Val (@! context.WithDeadline)) (Val #(interface.ok backgroundCtxVal))) (Val #d))
    {{ (ctx' : GoInterfaceOk) (γ' : ContextNames) (cancel : GoFunc),
        RET (PairV #(interface.ok ctx') #cancel);
        □ (∀ Φ : val → IProp GF, True -∗ ▷ (True -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        isContext ctx' (bgDeadlineDesc d γ') }} :=
  wp_WithDeadline_Background_of sync.Mutex.wp_Lock sync.Mutex.wp_Unlock
    sync.atomic.Value.wp_Load time.wp_Until time.wp_AfterFunc cancelCtx.wp_Done cancelCtx.wp_Err
    cancelCtx.wp_Value cancelCtx.wp_propagateCancel timerCtx.wp_cancel d

/-- `WithTimeout(Background(), tmo)` (see `wp_WithDeadlineCause_Background`): the deadline is
`time.Now().Add(tmo)`, some time `d`. -/
theorem wp_WithTimeout_Background (tmo : time.Duration) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context }}
      (App (App (Val (@! context.WithTimeout)) (Val #(interface.ok backgroundCtxVal)))
        (Val #tmo))
    {{ (ctx' : GoInterfaceOk) (γ' : ContextNames) (cancel : GoFunc) (d : time.Time),
        RET (PairV #(interface.ok ctx') #cancel);
        □ (∀ Φ : val → IProp GF, True -∗ ▷ (True -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        isContext ctx' (bgDeadlineDesc d γ') }} :=
  wp_WithTimeout_Background_of time.Time.wp_Add time.wp_Now sync.Mutex.wp_Lock
    sync.Mutex.wp_Unlock sync.atomic.Value.wp_Load time.wp_Until time.wp_AfterFunc
    cancelCtx.wp_Done cancelCtx.wp_Err cancelCtx.wp_Value cancelCtx.wp_propagateCancel
    timerCtx.wp_cancel tmo

end results

end context

end Perennial
