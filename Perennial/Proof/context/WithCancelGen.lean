/-
The other triples of `WithCancel`: `wp_WithCancel_gen_of`, for any spec of the new context's
`propagateCancel` (a second triple of `WithCancel`, proved from its code: `context.WithCancel.spec`
keeps the statement of `wp_WithCancel`, a `*cancelCtx` parent, which clients use, and the general
form cannot share its name), and from it `wp_WithCancel_any_of` (any `isContext` parent; used by
`WithDeadlineCause`) and `wp_WithCancel_Background_of` (`WithCancel(Background())`). The specs they
use are hypotheses; `Results.lean` has them under their old names, without them.
-/
module

public import Perennial.Proof.context.CancelCtxContext
public import Perennial.Proof.context.PropagateCancel
public import Perennial.Proof.context.BackgroundCtx
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

open ContextDesc

/-- `WithCancel(parent)`, given the spec of `c.propagateCancel(parent, c)` (see `wp_withCancel`):
the new `*cancelCtx` and its cancel function. -/
theorem wp_WithCancel_gen_of
    (wp_withCancel : context.withCancel.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_cancel : context.cancelCtx.cancel.spec (GF := GF) (hG := hG))
    (parent : GoInterfaceOk) (P Pre : IProp GF)
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
        ctxField c ↦□ (interface.ok parent : GoInterface) }} := by
  wp_start as ⟨#Hcci, Hpre, #Hpar⟩
  ihave #Hi := isInit_access $$ Hpkg
  icases Hi with ⟨_, _, ⟨%canceled, #Hcanceled, %hcanceled⟩, _⟩
  wp_auto
  iapply wp_fupd
  wp_apply wp_withCancel parent P Pre Hprop $$ [$Hcci $Hpre] as %c %γ ⟨#Hc, #Hf⟩
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

/-- `WithCancel(parent)` for any context `parent` (`isContext`): the new context is a
`*cancelCtx` with the parent's deadline whose cancel function needs nothing (so its Done
proposition is `True`). -/
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
        isContext ctx' { s with PDone := iprop(True), Done_gn := γ' } }} := by
  have childCancelSpec_cancelCtx := childCancelSpec_cancelCtx_of wp_cancelCtx_cancel
  have isContext_cancelCtx := isContext_cancelCtx_of wp_cancelCtx_Done wp_cancelCtx_Err
      wp_cancelCtx_Value wp_VLoad
  have wp_WithCancel_gen := wp_WithCancel_gen_of wp_withCancel wp_cancelCtx_cancel
  have wp_propagateCancel_any := wp_propagateCancel_any_of wp_propagateCancel
  iintro %Φ ⟨#Hpkg, #Hctx⟩ HΦ
  ihave #Hctx2 := Hctx
  iunfold isContext at Hctx2
  iunfold isContextDef at Hctx2
  icases Hctx2 with ⟨-, -, -, -, -, -, -, #Hcci⟩
  iapply wp_WithCancel_gen parent iprop(True) iprop(isContext parent s)
      (fun c γ => by
        iintro %Φ ⟨#Hpkg, #Hc, Hf, #Hctx⟩ HΦ
        ihave #Htt : □ (iprop(True) -∗ iprop(True)) $$ []
        · imodintro; iintro -; itrivial
        ihave #Hk := childCancelSpec_cancelCtx c γ iprop(True) iprop(True) $$ [$Hpkg $Hc $Htt]
        iapply wp_propagateCancel_any c parent s _ $$ [$Hpkg $Hf $Hctx $Hk] HΦ)
  · iframe #
    unfold isParentCtx; iright; iexists s; iframe #
  inext
  iintro %c %γ %cancel ⟨#Hcancel, #Hc, #Hf⟩
  ihave #Hdl := deadlineSpec_isContext _ _ $$ Hctx
  iapply HΦ $$ %(interface.mk (go.GoType.PointerType context.cancelCtx.ty) #c)
  isplitl []
  · iexact Hcancel
  · iapply isContext_cancelCtx c γ _ parent _ rfl rfl
    iframe #

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
        isCancelCtxCtx ctx' { Values := ∅, Deadline := none, Done_gn := γ', PDone := PDone' } }} := by
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

end wps

end context

end Perennial
