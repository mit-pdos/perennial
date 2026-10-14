/-
`context.cancelCtx.propagateCancel`'s spec.
-/
module

public import Perennial.Proof.context.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- `c.propagateCancel(parent, child)`: sets `c`'s `Context` field to `parent` (and registers
`child` with the parent, or cancels it). Three cases (three triples before, now derived from this
one in `PropagateCancel.lean`, as `wp_propagateCancel_background_of` etc., and under their old
names in `Results.lean`):
* `parent` is `Background()` and `child` is `c` (`wp_propagateCancel_background`):
  `c.propagateCancel(Background(), c)`: the parent is never canceled (`Done()` is `nil`).
* `child` is `c`, and `parent` a `*cancelCtx` (`wp_propagateCancel_cancelCtx`):
  `c.propagateCancel(parent, c)` for a parent that is a `*cancelCtx` described by `s` whose
  Done proposition implies `c`'s: either the parent is already done (then `c` is canceled at once),
  or `c` is added to the parent's `children` (with its `childCancelSpec`).
* any `isContext` parent (`wp_propagateCancel_any`):
  `c.propagateCancel(parent, child)` for any context `parent` (`isContext`) and a child whose
  `cancel(false, err, cause)` needs nothing but a typed error (`childCancelSpec True`): the child
  is canceled at once if the parent is done, and is otherwise added to the `children` of the
  `*cancelCtx` that `parentCancelCtx(parent)` finds (`"#HParentCC"`; the branches for other
  parents are not reached). -/
abbrev context.cancelCtx.propagateCancel.spec : Prop :=
  ∀ (c : Loc) (parent : GoInterfaceOk) (k : GoInterface)
      [SafeMapKey (GF := GF) context.canceler.ty k],
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗
        ctxField c ↦ (interface.nil : GoInterface) ∗
        (⌜parent = backgroundCtxVal ∧
            k = interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c⌝ ∨
         (∃ (γ : ContextNames) (P : IProp GF) (s : ContextDesc (IProp GF)),
            ⌜k = interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c⌝ ∗
            isCancelCtxOf c γ P ∗ isContext parent s ∗ isCancelCtxCtx parent s ∗
            □ (s.PDone -∗ P)) ∨
         (∃ s : ContextDesc (IProp GF), isContext parent s ∗ childCancelSpec iprop(True) k)) }}
      (App (App (Val (c @!! go.GoType.PointerType context.cancelCtx.ty @!! go!"propagateCancel"))
        (Val #(interface.ok parent)))
        (Val #k))
    {{ RET #(); ctxField c ↦ (interface.ok parent : GoInterface) }}

end spec

end Perennial
