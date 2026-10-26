/-
The three cases of `context.cancelCtx.propagateCancel.spec` (which were its three triples), from
the spec (a hypothesis; `Results.lean` has them under their old names, without it).
-/
module

public import Perennial.Proof.context.Base
public import Perennial.Spec.context.cancelCtx__propagateCancel

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

/-- `c.propagateCancel(Background(), child)` for any `child`: the parent is never canceled
(`Done()` is `nil`), and the child is not looked at (a `*timerCtx` registers itself as the child
of its `cancelCtx`, `WithDeadlineBackground.lean`). -/
theorem wp_propagateCancel_background_any_of
    (wp_propagateCancel : context.cancelCtx.propagateCancel.spec (GF := GF) (hG := hG))
    (c : Loc) (k : GoInterface) [SafeMapKey (GF := GF) context.canceler.ty k] :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗
        ctxField c ↦ (interface.nil : GoInterface) }}
      (App (App (Val (c @!! go.GoType.PointerType context.cancelCtx.ty @!! go!"propagateCancel"))
        (Val #(interface.ok backgroundCtxVal)))
        (Val #k))
    {{ RET #(); ctxField c ↦ (interface.ok backgroundCtxVal : GoInterface) }} := by
  iintro %Φ ⟨#Hpkg, Hf⟩ HΦ
  iapply wp_propagateCancel c backgroundCtxVal k $$ [Hf] HΦ
  isplitl []
  · iexact Hpkg
  isplitl [Hf]
  · iexact Hf
  ileft
  ipureintro
  rfl

/-- `c.propagateCancel(Background(), c)`: `wp_propagateCancel_background_any_of` with `c` as the
child. -/
theorem wp_propagateCancel_background_of
    (wp_propagateCancel : context.cancelCtx.propagateCancel.spec (GF := GF) (hG := hG))
    (c : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗
        ctxField c ↦ (interface.nil : GoInterface) }}
      (App (App (Val (c @!! go.GoType.PointerType context.cancelCtx.ty @!! go!"propagateCancel"))
        (Val #(interface.ok backgroundCtxVal)))
        (Val #(interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c)))
    {{ RET #(); ctxField c ↦ (interface.ok backgroundCtxVal : GoInterface) }} :=
  wp_propagateCancel_background_any_of wp_propagateCancel c _

/-- `c.propagateCancel(parent, c)` for a parent that is a `*cancelCtx` described by `s` whose
Done proposition implies `c`'s: either the parent is already done (then `c` is canceled at once),
or `c` is added to the parent's `children` (with its `childCancelSpec`). -/
theorem wp_propagateCancel_cancelCtx_of
    (wp_propagateCancel : context.cancelCtx.propagateCancel.spec (GF := GF) (hG := hG))
    (c : Loc) (γ : ContextNames) (P : IProp GF)
    (parent : GoInterfaceOk) (s : ContextDesc (IProp GF)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗
        ctxField c ↦ (interface.nil : GoInterface) ∗
        (isContext parent s ∗ isCancelCtxCtx parent s ∗ □ (s.PDone -∗ P)) }}
      (App (App (Val (c @!! go.GoType.PointerType context.cancelCtx.ty @!! go!"propagateCancel"))
        (Val #(interface.ok parent)))
        (Val #(interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c)))
    {{ RET #(); ctxField c ↦ (interface.ok parent : GoInterface) }} := by
  iintro %Φ ⟨#Hpkg, #Hc, Hf, #Hctx, #Hcc, #HPP⟩ HΦ
  iapply wp_propagateCancel c parent
    (interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c) $$ [Hf] HΦ
  isplitl []
  · iexact Hpkg
  isplitl [Hf]
  · iexact Hf
  iright
  ileft
  iexists γ, P, s
  isplitl []
  · ipureintro; rfl
  iframe #

/-- `c.propagateCancel(parent, child)` for any context `parent` (`isContext`) and a child whose
`cancel(false, err, cause)` needs nothing but a typed error (`childCancelSpec True`): the child
is canceled at once if the parent is done, and is otherwise added to the `children` of the
`*cancelCtx` that `parentCancelCtx(parent)` finds (`"#HParentCC"`; the branches for other
parents are not reached). -/
theorem wp_propagateCancel_any_of
    (wp_propagateCancel : context.cancelCtx.propagateCancel.spec (GF := GF) (hG := hG))
    (c : Loc) (parent : GoInterfaceOk) (s : ContextDesc (IProp GF))
    (k : GoInterface) [SafeMapKey (GF := GF) context.canceler.ty k] :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗
        ctxField c ↦ (interface.nil : GoInterface) ∗ isContext parent s ∗
        childCancelSpec iprop(True) k }}
      (App (App (Val (c @!! go.GoType.PointerType context.cancelCtx.ty @!! go!"propagateCancel"))
        (Val #(interface.ok parent)))
        (Val #k))
    {{ RET #(); ctxField c ↦ (interface.ok parent : GoInterface) }} := by
  iintro %Φ ⟨#Hpkg, Hf, #Hctx, #Hk⟩ HΦ
  iapply wp_propagateCancel c parent k $$ [Hf] HΦ
  isplitl []
  · iexact Hpkg
  isplitl [Hf]
  · iexact Hf
  iright
  iright
  iexists s
  iframe #

end wps

end context

end Perennial
