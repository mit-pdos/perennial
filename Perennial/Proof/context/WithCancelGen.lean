/-
The other triples of `WithCancel`: `wp_WithCancel_gen_of`, for any spec of the new context's
`propagateCancel` (a second triple of `WithCancel`, proved from its code: `context.WithCancel.spec`
keeps the statement of `wp_WithCancel`, a `*cancelCtx` parent, which clients use, and the general
form cannot share its name), and from it `wp_WithCancel_ctx_of` (any `isContext` parent, the new
context's Done proposition `parent.PDone ∨ PDone'`), its corollary `wp_WithCancel_any_of` (Done
proposition `True`; used by `WithDeadlineCause`), `wp_WithCancel_Background_of` (`WithCancel(Background())`),
`wp_WithCancel_genA_of` (`wp_WithCancel_gen_of` for a context with given allowed errors) and
`wp_WithCancel_Background_canceled_of` (`WithCancel(Background())`, whose cancel function makes
`Err()` return `Canceled`'s value: `errIsCanceled`)
and `wp_WithCancel_TODO_of` (`WithCancel(TODO())`). The specs they
use are hypotheses; `Results.lean` has them under their old names, without them.
-/
module

public import Perennial.Proof.context.CancelCtxContext
public import Perennial.Proof.context.PropagateCancel
public import Perennial.Proof.context.BackgroundCtx
public import Perennial.Proof.context.CtxValue
public import Perennial.Spec.context.withCancel_
public import Perennial.Spec.context.cancelCtx__cancel

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace context

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

open ContextDesc

/-- `WithCancel(parent)`, given the spec of `c.propagateCancel(parent, c)` (see `wp_withCancel`),
for a new `*cancelCtx` with allowed errors `A` (which must allow `Canceled`'s value, what its cancel
function cancels it with): the new `*cancelCtx` and its cancel function. -/
theorem wp_WithCancel_genA_of
    (wp_withCancel : context.withCancel.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_cancel : context.cancelCtx.cancel.spec (GF := GF) (hG := hG))
    (parent : GoInterfaceOk) (P Pre : IProp GF) (A : GoInterface → Prop)
    (Hprop : ∀ (c : Loc) (γ : ContextNames),
      {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOfA c γ P A ∗
          ctxField c ↦ (interface.nil : GoInterface) ∗ Pre }}
        (App (App (Val (c @!! go.GoType.PointerType context.cancelCtx.ty @!! go!"propagateCancel"))
          (Val #(interface.ok parent)))
          (Val #(interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c)))
      {{ RET #(); ctxField c ↦ (interface.ok parent : GoInterface) }}) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isClosedchanInit ∗ Pre ∗
        isParentCtx parent ∗
        □ (∀ e : GoInterface, globalAddr context.Canceled ↦□ e -∗ ⌜A e⌝) }}
      (App (Val (@! context.WithCancel)) (Val #(interface.ok parent)))
    {{ (c : Loc) (γ : ContextNames) (cancel : GoFunc),
        RET (PairV #(interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c) #cancel);
        cancelSpec cancel γ P ∗ isCancelCtxOfA c γ P A ∗
        ctxField c ↦□ (interface.ok parent : GoInterface) }} := by
  wp_start as ⟨#Hcci, Hpre, #Hpar, #HA⟩
  ihave #Hi := isInit_access $$ Hpkg
  icases Hi with ⟨_, _, ⟨%canceled, #Hcanceled, %hcanceled⟩, _⟩
  ihave #Hce := isCtxErr_of_Canceled _ $$ Hpkg Hcanceled
  ihave %hA := HA $$ %canceled Hcanceled
  wp_auto
  iapply wp_fupd
  wp_apply wp_withCancel parent P Pre A Hprop $$ [$Hcci $Hpre] as %c %γ ⟨#Hc, #Hf⟩
  ipersist c
  imodintro
  iapply HΦ
  iframe #
  unfold cancelSpec
  imodintro
  iintro %Φ' #Hp HΦ'
  wp_auto
  wp_apply wp_cancelCtx_cancel c γ P A true canceled GoInterface.nil hcanceled hA $$ [$Hc $Hce]
    as #Hclosed
  · iframe #
    simp only [↓reduceIte]
    iexists parent
    iframe #
  iapply HΦ' $$ Hclosed

/-- `WithCancel(parent)`, given the spec of `c.propagateCancel(parent, c)` (see `wp_withCancel`):
the new `*cancelCtx` (which any context error may cancel) and its cancel function. -/
theorem wp_WithCancel_gen_of
    (wp_withCancel : context.withCancel.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_cancel : context.cancelCtx.cancel.spec (GF := GF) (hG := hG))
    (parent : GoInterfaceOk) (P Pre : IProp GF)
    (Hprop : ∀ (c : Loc) (γ : ContextNames),
      {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOfA c γ P (fun _ => True) ∗
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
        ctxField c ↦□ (interface.ok parent : GoInterface) }} := by
  wp_start as ⟨#Hcci, Hpre, #Hpar⟩
  ihave #Hi := isInit_access $$ Hpkg
  icases Hi with ⟨_, _, ⟨%canceled, #Hcanceled, %hcanceled⟩, _⟩
  ihave #Hce := isCtxErr_of_Canceled _ $$ Hpkg Hcanceled
  wp_auto
  iapply wp_fupd
  wp_apply wp_withCancel parent P Pre (fun _ => True) Hprop $$ [$Hcci $Hpre] as %c %γ ⟨#HcA, #Hf⟩
  ihave #Hc := isCancelCtxOfA_of _ _ _ _ $$ HcA
  ipersist c
  imodintro
  iapply HΦ
  iframe #
  unfold cancelSpec
  imodintro
  iintro %Φ' #Hp HΦ'
  wp_auto
  wp_apply wp_cancelCtx_cancel c γ P (fun _ => True) true canceled GoInterface.nil hcanceled trivial
    $$ [$HcA $Hce]
    as #Hclosed
  · iframe #
    simp only [↓reduceIte]
    iexists parent
    iframe #
  iapply HΦ' $$ Hclosed

/-- `WithCancel(parent)` for any context `parent` (`isContext`, described by `s`) and any
proposition `PDone'`: the new context is a `*cancelCtx` with the parent's deadline, whose Done
proposition is `s.PDone ∨ PDone'` (it is done because its parent is, or because its cancel function
ran, which needs `□ PDone'`). -/
theorem wp_WithCancel_ctx_of
    (wp_withCancel : context.withCancel.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_cancel : context.cancelCtx.cancel.spec (GF := GF) (hG := hG))
    (wp_propagateCancel : context.cancelCtx.propagateCancel.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Done : context.cancelCtx.Done.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Err : context.cancelCtx.Err.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Value : context.cancelCtx.Value.spec (GF := GF) (hG := hG))
    (wp_VLoad : sync.atomic.Value.Load.spec (GF := GF) (hG := hG))
    (parent : GoInterfaceOk) (s : ContextDesc (IProp GF)) (PDone' : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isContext parent s }}
      (App (Val (@! context.WithCancel)) (Val #(interface.ok parent)))
    {{ (ctx' : GoInterfaceOk) (γ' : ContextNames) (cancel : GoFunc),
        RET (PairV #(interface.ok ctx') #cancel);
        cancelSpec cancel γ' PDone' ∗
        isContext ctx' { s with PDone := iprop(s.PDone ∨ PDone'), Done_gn := γ' } ∗
        isCancelCtxCtx ctx' { s with PDone := iprop(s.PDone ∨ PDone'), Done_gn := γ' } ∗
        ctxValueFrom parent ctx' }} := by
  have childCancelSpec_cancelCtx := childCancelSpec_cancelCtx_of wp_cancelCtx_cancel
  have isContext_cancelCtx := isContext_cancelCtx_of wp_cancelCtx_Done wp_cancelCtx_Err
      wp_cancelCtx_Value wp_VLoad
  have wp_WithCancel_gen := wp_WithCancel_gen_of wp_withCancel wp_cancelCtx_cancel
  have wp_propagateCancel_ctx := wp_propagateCancel_ctx_of wp_propagateCancel
  iintro %Φ ⟨#Hpkg, #Hctx⟩ HΦ
  ihave #Hctx2 := Hctx
  iunfold isContext at Hctx2
  iunfold isContextDef at Hctx2
  icases Hctx2 with ⟨-, -, -, -, -, -, -, #Hcci⟩
  iapply wp_WithCancel_gen parent iprop(s.PDone ∨ PDone') iprop(isContext parent s)
      (fun c γ => by
        iintro %Φ ⟨#Hpkg, #Hc, Hf, #Hctx⟩ HΦ
        ihave #Hl : □ (s.PDone -∗ iprop(s.PDone ∨ PDone')) $$ []
        · imodintro; iintro Hp; ileft; iexact Hp
        ihave #Hk := childCancelSpec_cancelCtx c γ iprop(s.PDone ∨ PDone') s.PDone $$
          [$Hpkg $Hc $Hl]
        iapply wp_propagateCancel_ctx c parent s _ $$ [$Hpkg $Hf $Hctx $Hk] HΦ)
  · iframe #
    unfold isParentCtx; iright; iexists s; iframe #
  inext
  iintro %c %γ %cancel ⟨#Hcancel, #Hc, #Hf⟩
  ihave #Hdl := deadlineSpec_isContext _ _ $$ Hctx
  iapply HΦ $$ %(interface.mk (go.GoType.PointerType context.cancelCtx.ty) #c)
  isplitl []
  · unfold cancelSpec
    imodintro
    iintro %Φ' #Hp HΦ'
    iapply Hcancel
    · imodintro; iright; iexact Hp
    iexact HΦ'
  isplitl []
  · iapply isContext_cancelCtx c γ _ parent _ rfl rfl
    iframe #
  isplitl []
  · unfold isCancelCtxCtx; iexists c; iframe #; ipureintro; rfl
  · iapply ctxValueFrom_cancel c parent; iexact Hf

/-- `WithCancel(parent)` for any context `parent` (`isContext`): `wp_WithCancel_ctx_of` with
`PDone' := True`, the new context's Done proposition weakened to `True` (its cancel function
needs nothing). -/
theorem wp_WithCancel_any_of
    (wp_withCancel : context.withCancel.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_cancel : context.cancelCtx.cancel.spec (GF := GF) (hG := hG))
    (wp_propagateCancel : context.cancelCtx.propagateCancel.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Done : context.cancelCtx.Done.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Err : context.cancelCtx.Err.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Value : context.cancelCtx.Value.spec (GF := GF) (hG := hG))
    (wp_VLoad : sync.atomic.Value.Load.spec (GF := GF) (hG := hG))
    (parent : GoInterfaceOk) (s : ContextDesc (IProp GF)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isContext parent s }}
      (App (Val (@! context.WithCancel)) (Val #(interface.ok parent)))
    {{ (ctx' : GoInterfaceOk) (γ' : ContextNames) (cancel : GoFunc),
        RET (PairV #(interface.ok ctx') #cancel);
        cancelSpec cancel γ' iprop(True) ∗
        isContext ctx' { s with PDone := iprop(True), Done_gn := γ' } ∗
        ctxValueFrom parent ctx' }} := by
  iintro %Φ ⟨#Hpkg, #Hctx⟩ HΦ
  iapply wp_WithCancel_ctx_of wp_withCancel wp_cancelCtx_cancel wp_propagateCancel
    wp_cancelCtx_Done wp_cancelCtx_Err wp_cancelCtx_Value wp_VLoad parent s iprop(True)
    $$ [$Hpkg $Hctx]
  inext
  iintro %ctx' %γ' %cancel ⟨#Hcancel, #Hc, -, #Hv⟩
  iapply HΦ
  iframe #
  iapply isContext_weaken ctx' { s with PDone := iprop(s.PDone ∨ True), Done_gn := γ' }
    iprop(True) $$ [] Hc
  imodintro; iintro -; itrivial

/-- `WithCancel(Background())`: as `wp_WithCancel`, for a parent that is never done, with no
values and no deadline (so the new context's `PDone` is just `PDone'`, which the cancel function
needs). -/
theorem wp_WithCancel_Background_of
    (wp_withCancel : context.withCancel.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_cancel : context.cancelCtx.cancel.spec (GF := GF) (hG := hG))
    (wp_propagateCancel : context.cancelCtx.propagateCancel.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Done : context.cancelCtx.Done.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Err : context.cancelCtx.Err.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Value : context.cancelCtx.Value.spec (GF := GF) (hG := hG))
    (wp_VLoad : sync.atomic.Value.Load.spec (GF := GF) (hG := hG))
    (PDone' : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isClosedchanInit }}
      (App (Val (@! context.WithCancel)) (Val #(interface.ok backgroundCtxVal)))
    {{ (ctx' : GoInterfaceOk) (γ' : ContextNames) (cancel : GoFunc),
        RET (PairV #(interface.ok ctx') #cancel);
        □ (∀ Φ : val → IProp GF, □ PDone' -∗ ▷ (ContextClosed γ' -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        isContext ctx' { Values := ∅, Deadline := none, Done_gn := γ', PDone := PDone' } ∗
        isCancelCtxCtx ctx' { Values := ∅, Deadline := none, Done_gn := γ', PDone := PDone' } ∗
        ctxValueFrom backgroundCtxVal ctx' }} := by
  have isContext_cancelCtx := isContext_cancelCtx_of wp_cancelCtx_Done wp_cancelCtx_Err
      wp_cancelCtx_Value wp_VLoad
  have wp_WithCancel_gen := wp_WithCancel_gen_of wp_withCancel wp_cancelCtx_cancel
  have wp_propagateCancel_background := wp_propagateCancel_background_of wp_propagateCancel
  iintro %Φ ⟨#Hpkg, #Hcci⟩ HΦ
  iapply wp_WithCancel_gen backgroundCtxVal PDone' iprop(True)
      (fun c γ => by
        iintro %Φ ⟨#Hpkg, -, Hf, -⟩ HΦ
        iapply wp_propagateCancel_background c $$ [$Hpkg $Hf] HΦ)
  · iframe #
    isplitl []
    · itrivial
    unfold isParentCtx; ileft; ipureintro; exact Or.inl rfl
  inext
  iintro %c %γ %cancel ⟨#Hcancel, #Hc, #Hf⟩
  ihave #Hdl := deadlineSpec_background (GF := GF)
  iapply HΦ $$ %(interface.mk (go.GoType.PointerType context.cancelCtx.ty) #c)
  isplitl []
  · unfold cancelSpec; iexact Hcancel
  isplitl []
  · iapply isContext_cancelCtx c γ PDone' backgroundCtxVal _ rfl rfl
    iframe #
  isplitl []
  · unfold isCancelCtxCtx; iexists c; iframe #; ipureintro; rfl
  · iapply ctxValueFrom_cancel c backgroundCtxVal; iexact Hf

/-- `WithCancel(TODO())`: as `wp_WithCancel_Background_of` (`TODO()`, like `Background()`, is
never done and has no values and no deadline) (so the new context's `PDone` is just `PDone'`, which the cancel function
needs). -/
theorem wp_WithCancel_TODO_of
    (wp_withCancel : context.withCancel.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_cancel : context.cancelCtx.cancel.spec (GF := GF) (hG := hG))
    (wp_propagateCancel : context.cancelCtx.propagateCancel.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Done : context.cancelCtx.Done.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Err : context.cancelCtx.Err.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Value : context.cancelCtx.Value.spec (GF := GF) (hG := hG))
    (wp_VLoad : sync.atomic.Value.Load.spec (GF := GF) (hG := hG))
    (PDone' : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isClosedchanInit }}
      (App (Val (@! context.WithCancel)) (Val #(interface.ok todoCtxVal)))
    {{ (ctx' : GoInterfaceOk) (γ' : ContextNames) (cancel : GoFunc),
        RET (PairV #(interface.ok ctx') #cancel);
        □ (∀ Φ : val → IProp GF, □ PDone' -∗ ▷ (ContextClosed γ' -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        isContext ctx' { Values := ∅, Deadline := none, Done_gn := γ', PDone := PDone' } ∗
        isCancelCtxCtx ctx' { Values := ∅, Deadline := none, Done_gn := γ', PDone := PDone' } ∗
        ctxValueFrom todoCtxVal ctx' }} := by
  have isContext_cancelCtx := isContext_cancelCtx_of wp_cancelCtx_Done wp_cancelCtx_Err
      wp_cancelCtx_Value wp_VLoad
  have wp_WithCancel_gen := wp_WithCancel_gen_of wp_withCancel wp_cancelCtx_cancel
  have wp_propagateCancel_todo := wp_propagateCancel_todo_of wp_propagateCancel
  iintro %Φ ⟨#Hpkg, #Hcci⟩ HΦ
  iapply wp_WithCancel_gen todoCtxVal PDone' iprop(True)
      (fun c γ => by
        iintro %Φ ⟨#Hpkg, -, Hf, -⟩ HΦ
        iapply wp_propagateCancel_todo c $$ [$Hpkg $Hf] HΦ)
  · iframe #
    isplitl []
    · itrivial
    unfold isParentCtx; ileft; ipureintro; exact Or.inr rfl
  inext
  iintro %c %γ %cancel ⟨#Hcancel, #Hc, #Hf⟩
  ihave #Hdl := deadlineSpec_todo (GF := GF)
  iapply HΦ $$ %(interface.mk (go.GoType.PointerType context.cancelCtx.ty) #c)
  isplitl []
  · unfold cancelSpec; iexact Hcancel
  isplitl []
  · iapply isContext_cancelCtx c γ PDone' todoCtxVal _ rfl rfl
    iframe #
  isplitl []
  · unfold isCancelCtxCtx; iexists c; iframe #; ipureintro; rfl
  · iapply ctxValueFrom_cancel c todoCtxVal; iexact Hf

/-- **`WithCancel(Background())`, with what its cancel function leaves**: as
`wp_WithCancel_Background_of` (with `PDone' := True`), and the cancel function also makes the new
context's `Err()` return `Canceled`'s value for good (`errIsCanceled`). True of Go: `cancel` runs
`c.cancel(true, Canceled, nil)`, which stores `Canceled` in `c.err` unless it is set, and nothing
else sets it: `Background()`'s `Done()` is `nil`, so `propagateCancel` registers `c` with no parent,
and `c` is in no `children` map. The proof allocates `c` with allowed errors `(· = Canceled's
value)` (`wp_WithCancel_genA_of`): the only right to cancel it is its cancel function's. The new
context's `Context` field is `Background()` (`ctxField`). -/
theorem wp_WithCancel_Background_canceled_of
    (wp_withCancel : context.withCancel.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_cancel : context.cancelCtx.cancel.spec (GF := GF) (hG := hG))
    (wp_propagateCancel : context.cancelCtx.propagateCancel.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Done : context.cancelCtx.Done.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Err : context.cancelCtx.Err.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Value : context.cancelCtx.Value.spec (GF := GF) (hG := hG))
    (wp_VLoad : sync.atomic.Value.Load.spec (GF := GF) (hG := hG)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context }}
      (App (Val (@! context.WithCancel)) (Val #(interface.ok backgroundCtxVal)))
    {{ (c : Loc) (γ : ContextNames) (cancel : GoFunc),
        RET (PairV #(interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c) #cancel);
        □ (∀ Φ : val → IProp GF,
            ▷ (ContextClosed γ -∗
                errIsCanceled (interface.mk (go.GoType.PointerType context.cancelCtx.ty) #c) -∗
                Φ #()) -∗
            WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        isContext (interface.mk (go.GoType.PointerType context.cancelCtx.ty) #c)
          { Values := ∅, Deadline := none, Done_gn := γ, PDone := iprop(True) } ∗
        isCancelCtxCtx (interface.mk (go.GoType.PointerType context.cancelCtx.ty) #c)
          { Values := ∅, Deadline := none, Done_gn := γ, PDone := iprop(True) } ∗
        ctxField c ↦□ (interface.ok backgroundCtxVal : GoInterface) }} := by
  have isContext_cancelCtx := isContext_cancelCtx_of wp_cancelCtx_Done wp_cancelCtx_Err
      wp_cancelCtx_Value wp_VLoad
  have wp_WithCancel_genA := wp_WithCancel_genA_of wp_withCancel wp_cancelCtx_cancel
  have wp_propagateCancel_background := wp_propagateCancel_background_of wp_propagateCancel
  iintro %Φ #Hpkg HΦ
  ihave #Hcci := isClosedchanInit_of_init $$ Hpkg
  ihave #Hi := isInit_access $$ Hpkg
  icases Hi with ⟨_, _, ⟨%canceled, #Hcanceled, %hcanceled⟩, _⟩
  iapply wp_WithCancel_genA backgroundCtxVal iprop(True) iprop(True) (fun e => e = canceled)
      (fun c γ => by
        iintro %Φ ⟨#Hpkg, -, Hf, -⟩ HΦ
        iapply wp_propagateCancel_background c $$ [$Hpkg $Hf] HΦ)
  · iframe #
    isplitl []
    · itrivial
    isplitl []
    · unfold isParentCtx; ileft; ipureintro; exact Or.inl rfl
    imodintro
    iintro %e #He
    icombine He Hcanceled gives %h
    ipureintro; exact h
  inext
  iintro %c %γ %cancel ⟨#Hcancel, #Hc, #Hf⟩
  ihave #Hcw := isCancelCtxOfA_of _ _ _ _ $$ Hc
  ihave #Hdl := deadlineSpec_background (GF := GF)
  iunfold cancelSpec at Hcancel
  iapply HΦ
  isplitl []
  · imodintro
    iintro %Φ' HΦ'
    iapply Hcancel
    · imodintro; itrivial
    inext
    iintro #Hclosed
    iapply HΦ' $$ Hclosed
    unfold errIsCanceled
    iexists canceled
    isplitl []
    · iexact Hcanceled
    imodintro
    iintro %Φ'' HΦ''
    iapply wp_cancelCtx_Err c γ iprop(True) (fun e => e = canceled) true $$ [$Hpkg $Hc]
    · simp only [↓reduceIte]; iexact Hclosed
    inext
    iintro %e ⟨%hne, He⟩
    have hne := hne rfl
    simp only [hne, ↓reduceIte]
    icases He with ⟨-, -, -, -, %hA⟩
    have hA' : e = canceled := hA
    subst hA'
    iexact HΦ''
  isplitl []
  · iapply isContext_cancelCtx c γ iprop(True) backgroundCtxVal _ rfl rfl
    iframe #
  isplitl []
  · unfold isCancelCtxCtx; iexists c; iframe #; ipureintro; rfl
  · iexact Hf

end wps

end context

end Perennial
