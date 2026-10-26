/-
`context.parentCancelCtx`'s spec.
-/
module

public import Perennial.Proof.context.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- The postcondition in the `ok` case is `isCancelCtx ctx` (persistent
knowledge that `ctx` is a valid shared `*cancelCtx`), not `∃ c, ctx ↦ c`. The returned `*cancelCtx` is
shared with every other user of the parent context (its fields are protected
by `ctx.mu` or are atomics), so full ownership of its points-to cannot be
returned.

(The cases of `Background()`, a `*cancelCtx` and a `*timerCtx` parent with an exact result are the
shared lemmas `wp_parentCancelCtx_background`, `wp_parentCancelCtx_self_of` and
`wp_parentCancelCtx_timer_of`, which the proofs of the `isContext`s of these contexts use.) -/
abbrev context.parentCancelCtx.spec : Prop :=
  ∀ (parent : GoInterfaceOk) (parent_desc : ContextDesc (IProp GF)),
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗
        "#Hctx" ∷ isContext parent parent_desc }}
      (App (Val (@! context.parentCancelCtx)) (Val #(interface.ok parent)))
    {{ (ctx : Loc) (ok : Bool), RET (PairV #ctx #ok);
        if ok then isCancelCtx ctx
        else iprop(⌜ctx = Loc.null⌝) }}

end spec

end Perennial
