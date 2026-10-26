/-
The proof of `context.WithCancel` (for a `*cancelCtx` parent, from `wp_WithCancel_gen_of`).
-/
module

public import Perennial.Spec.context.WithCancel
public import Perennial.Spec.sync.atomic.Value__Load
public import Perennial.Spec.context.cancelCtx__Done
public import Perennial.Spec.context.cancelCtx__Err
public import Perennial.Spec.context.cancelCtx__Value
public import Perennial.Spec.context.cancelCtx__cancel
public import Perennial.Spec.context.cancelCtx__propagateCancel
public import Perennial.Spec.context.withCancel_
public import Perennial.Proof.context.CancelCtxContext
public import Perennial.Proof.context.PropagateCancel
public import Perennial.Proof.context.WithCancelGen

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- From `wp_WithCancel_gen_of`, with the parent's `propagateCancel`
(`wp_propagateCancel_cancelCtx_of`). -/
theorem context.WithCancel.wp_proof
    (wp_VLoad : sync.atomic.Value.Load.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Done : context.cancelCtx.Done.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Err : context.cancelCtx.Err.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_Value : context.cancelCtx.Value.spec (GF := GF) (hG := hG))
    (wp_cancelCtx_cancel : context.cancelCtx.cancel.spec (GF := GF) (hG := hG))
    (wp_propagateCancel : context.cancelCtx.propagateCancel.spec (GF := GF) (hG := hG))
    (wp_withCancel : context.withCancel.spec (GF := GF) (hG := hG)) :
    context.WithCancel.spec (GF := GF) (hG := hG) := fun PDone' ctx ctx_desc => by
  have isContext_cancelCtx := isContext_cancelCtx_of wp_cancelCtx_Done wp_cancelCtx_Err
      wp_cancelCtx_Value wp_VLoad
  have wp_WithCancel_gen := wp_WithCancel_gen_of wp_withCancel wp_cancelCtx_cancel
  have wp_propagateCancel_cancelCtx := wp_propagateCancel_cancelCtx_of wp_propagateCancel
  iintro %Φ ⟨#Hpkg, #Hctx, #Hcc⟩ HΦ
  ihave #Hcc' := Hcc
  iunfold isCancelCtxCtx at Hcc'
  icases Hcc' with ⟨%p, %hp, #Hpc⟩
  ihave #Hcci := isCancelCtxOf_closedchan _ _ _ $$ Hpc
  iapply wp_WithCancel_gen ctx iprop(ctx_desc.PDone ∨ PDone')
      iprop(isContext ctx ctx_desc ∗ isCancelCtxCtx ctx ctx_desc ∗
        □ (ctx_desc.PDone -∗ iprop(ctx_desc.PDone ∨ PDone')))
      (fun c γ => wp_propagateCancel_cancelCtx c γ _ ctx ctx_desc)
  · iframe #
    isplitl []
    · imodintro; iintro H; ileft; iexact H
    unfold isParentCtx; iright; iexists ctx_desc; iframe #
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

end proof

end Perennial
