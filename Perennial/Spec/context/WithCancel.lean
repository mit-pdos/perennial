/-
`context.WithCancel`'s spec.
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

/-- `WithCancel(ctx)` for a parent `ctx` that is a `*cancelCtx` made by `WithCancel`
(`isCancelCtxCtx`). The new context's Done channel does not exist yet when `WithCancel` returns,
so the postcondition gives fresh ghost names `γ'` for it. The cancel function's precondition is
`□ PDone'` (closing the Done channel needs the persistent Done proposition); it makes the new
context done (`ContextClosed γ'`). Observers of the new context's Done channel get
`□ (ctx_desc.PDone ∨ PDone')`: it is closed by the cancel function or when the parent is
canceled (the new context is in the parent's `children`).

(Other triples of `WithCancel` (`wp_WithCancel_gen`, for any `propagateCancel` spec, from which this
one and `wp_WithCancel_any`, `wp_WithCancel_Background` are derived) are in `WithCancelGen.lean` and
`Results.lean`.) -/
abbrev context.WithCancel.spec : Prop :=
  ∀ (PDone' : IProp GF) (ctx : GoInterfaceOk) (ctx_desc : ContextDesc (IProp GF)),
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isContext ctx ctx_desc ∗
        isCancelCtxCtx ctx ctx_desc }}
      (App (Val (@! context.WithCancel)) (Val #(interface.ok ctx)))
    {{ (ctx' : GoInterfaceOk) (γ' : ContextNames) (cancel : GoFunc),
        RET (PairV #(interface.ok ctx') #cancel);
        □ (∀ Φ : val → IProp GF, □ PDone' -∗ ▷ (ContextClosed γ' -∗ Φ #()) -∗
          WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
        isContext ctx' { ctx_desc with PDone := iprop(ctx_desc.PDone ∨ PDone'), Done_gn := γ' } ∗
        isCancelCtxCtx ctx'
          { ctx_desc with PDone := iprop(ctx_desc.PDone ∨ PDone'), Done_gn := γ' } }}

end spec

end Perennial
