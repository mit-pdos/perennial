/-
`WithDeadlineCause`, `WithDeadline` and `WithTimeout` of `context.Background()`.

`context.WithDeadlineCause.spec` takes an `isContext` parent, which `Background()`'s value is not
(its `Done()` is `nil`, its `Deadline()` returns no deadline). These are the counterparts of
`wp_WithCancel_Background` (`WithCancelGen.lean`) for the deadline constructors, for the common Go
idiom `ctx, cancel := context.WithTimeout(context.Background(), timeout)`: the new context is a
`*timerCtx` whose parent is `Background()`, so it has no values, the deadline given (`WithTimeout`:
`time.Now().Add(timeout)`, some time `d`) and the Done proposition `True`, and its `cancel`
function needs nothing. Only `isPkgInit` is required: `closedchan` is closed once `context` is
initialized (`isClosedchanInit_of_init`).

The proof of `wp_WithDeadlineCause_Background_of` is `WithDeadlineCause.wp_proof`'s no-deadline
branch with the parent's facts replaced by `Background()`'s: `deadlineSpec_background` for the
parent's `Deadline()`, `wp_propagateCancel_background_any` for `propagateCancel` (nothing to
register with a parent that is never done), and `isParentCtx`'s `Background()` case for `timerCtx.cancel`.
-/
module

public import Perennial.Spec.context.WithDeadlineCause
public import Perennial.Spec.context.WithDeadline
public import Perennial.Spec.context.WithTimeout
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Spec.sync.atomic.Value__Load
public import Perennial.Spec.time.Until
public import Perennial.Spec.time.AfterFunc
public import Perennial.Spec.time.Time__Add
public import Perennial.Spec.time.Now
public import Perennial.Spec.context.cancelCtx__Done
public import Perennial.Spec.context.cancelCtx__Err
public import Perennial.Spec.context.cancelCtx__Value
public import Perennial.Spec.context.cancelCtx__propagateCancel
public import Perennial.Spec.context.timerCtx__cancel
public import Perennial.Proof.context.CancelCtxCells
public import Perennial.Proof.context.TimerCtx
public import Perennial.Proof.context.PropagateCancel
public import Perennial.Proof.context.BackgroundCtx

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace context

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- The descriptor of a context made from `Background()` with the deadline `d`: no values, the
deadline `d`, Done names `γ'`, Done proposition `True`. -/
abbrev bgDeadlineDesc (d : time.Time) (γ' : ContextNames) : ContextDesc (IProp GF) :=
  { Values := ∅, Deadline := some d, Done_gn := γ', PDone := iprop(True) }

/-- `WithDeadlineCause(Background(), d, cause)` (see the file header). -/
theorem wp_WithDeadlineCause_Background_of
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_VLoad : sync.atomic.Value.Load.spec (GF := GF) (hG := hG))
    (wp_Until : time.Until.spec (GF := GF) (hG := hG))
    (wp_AfterFunc : time.AfterFunc.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Done : context.cancelCtx.Done.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Err : context.cancelCtx.Err.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Value : context.cancelCtx.Value.spec (GF := GF) (hG := hG))
    (wp_propagateCancel : context.cancelCtx.propagateCancel.spec (GF := GF) (hG := hG))
    (wp_timerCtx_cancel : context.timerCtx.cancel.spec (GF := GF) (hG := hG))
    (d : time.Time) (cause : GoError) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context }}
      (App (App (App (Val (@! context.WithDeadlineCause)) (Val #(interface.ok backgroundCtxVal)))
        (Val #d)) (Val #cause))
    {{ (ctx' : GoInterfaceOk) (γ' : ContextNames) (cancel : GoFunc),
        RET (PairV #(interface.ok ctx') #cancel);
        □ (∀ Φ : val → IProp GF, True -∗ ▷ (True -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        isContext ctx' (bgDeadlineDesc d γ') }} := by
  have wp_err_Load := wp_err_Load_of wp_VLoad
  have isContext_timerCtx := isContext_timerCtx_of wp_cancelCtx_Done wp_cancelCtx_Err
      wp_cancelCtx_Value wp_VLoad
  have wp_propagateCancel_background := wp_propagateCancel_background_any_of wp_propagateCancel
  wp_start
  ihave #Hcci := isClosedchanInit_of_init $$ Hpkg
  ihave #Hi := isInit_access $$ Hpkg
  icases Hi with ⟨_, _, ⟨%canceled, #Hcanceled, %hcanceled⟩, ⟨%dexc, #Hdexc, %hdexc⟩, _⟩
  ihave #HDeadline := deadlineSpec_background (GF := GF)
  iunfold deadlineSpec at HDeadline
  iapply wp_with_defer
  iintro %defer Hdefer
  wp_auto
  wp_apply HDeadline
  dsimp only [Option.getD]
  (try wp_auto)
  iStructNamedPrefix «$r0» "T"
  ipersist c
  ipersist cause
  ihave HtR : timerR «$r0_ptr» $$ [Ttimer]
  · unfold timerR; iexists _; iframe; ileft; ipureintro; rfl
  imod cancelCtx_alloc (tcc «$r0_ptr») iprop(True) (timerR «$r0_ptr») $$ Hcci TcancelCtx HtR
    with ⟨%γ, #Hc, Hf⟩
  ipersist Tdeadline
  wp_apply wp_propagateCancel_background (tcc «$r0_ptr») _ $$ [$Hpkg $Hf] as Hf
  ipersist Hf
  ihave #Hc' := isCancelCtxOfR_of _ _ _ _ $$ Hc
  wp_apply wp_Until as %dur -
  wp_if_destruct
  · wp_apply wp_timerCtx_cancel «$r0_ptr» γ true dexc cause hdexc $$ [$Hc] as -
    · simp only [↓reduceIte]
      iexists backgroundCtxVal; iframe #
      unfold isParentCtx; ileft; ipureintro; rfl
    simp only [recv_eq_func_mk]
    iapply HΦ $$ %(interface.mk (go.GoType.PointerType context.timerCtx.ty) #«$r0_ptr») %γ
    isplitl []
    · imodintro
      iintro %Φ' - HΦ'
      wp_auto
      wp_apply wp_timerCtx_cancel «$r0_ptr» γ false canceled GoInterface.nil hcanceled $$ [$Hc]
        as -
      · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      iapply HΦ' $$ []; itrivial
    · iapply isContext_timerCtx «$r0_ptr» γ d _ rfl rfl rfl
      iframe #
  · ihave #Hc2 := Hc
    iunfold isCancelCtxOfR at Hc2
    icases Hc2 with ⟨#Hmu, -, -⟩
    wp_apply wp_Lock $$ [$Hmu] as ⟨Hlocked, Hlk⟩
    iunfold cancelCtxLockInv at Hlk
    icases Hlk with ⟨%children, %cause0, %od, %closed, Hchildren, Hcause, Hcl, Hod, HR⟩
    iunfold timerR at HR
    icases HR with ⟨%tm0, Htm0, Htm0r⟩
    wp_apply wp_err_Load (tcc «$r0_ptr») γ iprop(True) false $$ [$Hc'] as %e ⟨-, -⟩
    · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    cases e with
    | nil =>
      wp_auto
      wp_apply wp_AfterFunc as %tm #Htm
      · wp_auto
        wp_apply wp_timerCtx_cancel «$r0_ptr» γ true dexc cause hdexc $$ [$Hc] as -
        · simp only [↓reduceIte]
          iexists backgroundCtxVal; iframe #
          unfold isParentCtx; ileft; ipureintro; rfl
        itrivial
      wp_apply wp_Unlock $$ [$Hmu $Hlocked Hchildren Hcause Hcl Hod Htm0]
      · inext; unfold cancelCtxLockInv; iexists children, cause0, od, closed; iframe
        unfold timerR; iexists tm; iframe; iright; iexact Htm
      simp only [recv_eq_func_mk]
      iapply HΦ $$ %(interface.mk (go.GoType.PointerType context.timerCtx.ty) #«$r0_ptr») %γ
      isplitl []
      · imodintro
        iintro %Φ' - HΦ'
        wp_auto
        wp_apply wp_timerCtx_cancel «$r0_ptr» γ true canceled GoInterface.nil hcanceled $$ [$Hc]
          as -
        · simp only [↓reduceIte]
          iexists backgroundCtxVal; iframe #
          unfold isParentCtx; ileft; ipureintro; rfl
        iapply HΦ' $$ []; itrivial
      · iapply isContext_timerCtx «$r0_ptr» γ d _ rfl rfl rfl
        iframe #
    | ok ie =>
      wp_auto
      wp_apply wp_Unlock $$ [$Hmu $Hlocked Hchildren Hcause Hcl Hod Htm0 Htm0r]
      · inext; unfold cancelCtxLockInv; iexists children, cause0, od, closed; iframe
        unfold timerR; iexists tm0; iframe
      simp only [recv_eq_func_mk]
      iapply HΦ $$ %(interface.mk (go.GoType.PointerType context.timerCtx.ty) #«$r0_ptr») %γ
      isplitl []
      · imodintro
        iintro %Φ' - HΦ'
        wp_auto
        wp_apply wp_timerCtx_cancel «$r0_ptr» γ true canceled GoInterface.nil hcanceled $$ [$Hc]
          as -
        · simp only [↓reduceIte]
          iexists backgroundCtxVal; iframe #
          unfold isParentCtx; ileft; ipureintro; rfl
        iapply HΦ' $$ []; itrivial
      · iapply isContext_timerCtx «$r0_ptr» γ d _ rfl rfl rfl
        iframe #

/-- `WithDeadline(Background(), d)`: `WithDeadlineCause(Background(), d, nil)`. -/
theorem wp_WithDeadline_Background_of
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_VLoad : sync.atomic.Value.Load.spec (GF := GF) (hG := hG))
    (wp_Until : time.Until.spec (GF := GF) (hG := hG))
    (wp_AfterFunc : time.AfterFunc.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Done : context.cancelCtx.Done.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Err : context.cancelCtx.Err.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Value : context.cancelCtx.Value.spec (GF := GF) (hG := hG))
    (wp_propagateCancel : context.cancelCtx.propagateCancel.spec (GF := GF) (hG := hG))
    (wp_timerCtx_cancel : context.timerCtx.cancel.spec (GF := GF) (hG := hG))
    (d : time.Time) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context }}
      (App (App (Val (@! context.WithDeadline)) (Val #(interface.ok backgroundCtxVal))) (Val #d))
    {{ (ctx' : GoInterfaceOk) (γ' : ContextNames) (cancel : GoFunc),
        RET (PairV #(interface.ok ctx') #cancel);
        □ (∀ Φ : val → IProp GF, True -∗ ▷ (True -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        isContext ctx' (bgDeadlineDesc d γ') }} := by
  have wp_WDC := wp_WithDeadlineCause_Background_of wp_Lock wp_Unlock wp_VLoad wp_Until
    wp_AfterFunc wp_cancelCtx_Done wp_cancelCtx_Err wp_cancelCtx_Value wp_propagateCancel
    wp_timerCtx_cancel
  wp_start
  wp_auto
  wp_apply (wp_WDC d _) as %ctx' %γ' %cancel ⟨#Hcancel, #Hctx'⟩
  wp_end
  iframe #

/-- `WithTimeout(Background(), timeout)`: `WithDeadline(Background(), time.Now().Add(timeout))`,
some deadline `d`. -/
theorem wp_WithTimeout_Background_of
    (wp_TAdd : time.Time.Add.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_VLoad : sync.atomic.Value.Load.spec (GF := GF) (hG := hG))
    (wp_Until : time.Until.spec (GF := GF) (hG := hG))
    (wp_AfterFunc : time.AfterFunc.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Done : context.cancelCtx.Done.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Err : context.cancelCtx.Err.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Value : context.cancelCtx.Value.spec (GF := GF) (hG := hG))
    (wp_propagateCancel : context.cancelCtx.propagateCancel.spec (GF := GF) (hG := hG))
    (wp_timerCtx_cancel : context.timerCtx.cancel.spec (GF := GF) (hG := hG))
    (tmo : time.Duration) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context }}
      (App (App (Val (@! context.WithTimeout)) (Val #(interface.ok backgroundCtxVal)))
        (Val #tmo))
    {{ (ctx' : GoInterfaceOk) (γ' : ContextNames) (cancel : GoFunc) (d : time.Time),
        RET (PairV #(interface.ok ctx') #cancel);
        □ (∀ Φ : val → IProp GF, True -∗ ▷ (True -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        isContext ctx' (bgDeadlineDesc d γ') }} := by
  have wp_WD := wp_WithDeadline_Background_of wp_Lock wp_Unlock wp_VLoad wp_Until
    wp_AfterFunc wp_cancelCtx_Done wp_cancelCtx_Err wp_cancelCtx_Value wp_propagateCancel
    wp_timerCtx_cancel
  wp_start
  wp_auto
  wp_apply wp_Now as %now -
  wp_apply wp_TAdd as %d -
  wp_apply (wp_WD d) as %ctx' %γ' %cancel ⟨#Hcancel, #Hctx'⟩
  wp_end
  iframe #

end proof

end context

end Perennial
