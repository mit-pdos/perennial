/-
`context.withCancel`'s spec.
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

/-- `withCancel(parent)`, given the spec of `c.propagateCancel(parent, c)` for the new `c` (with
`Pre`): allocates the `*cancelCtx` `c` with fresh ghost names `γ` and Done proposition `P`, and
sets its parent. -/
abbrev context.withCancel.spec : Prop :=
  ∀ (parent : GoInterfaceOk) (P Pre : IProp GF),
    (∀ (c : Loc) (γ : ContextNames),
      {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗
          ctxField c ↦ (interface.nil : GoInterface) ∗ Pre }}
        (App (App (Val (c @!! go.GoType.PointerType context.cancelCtx.ty @!! go!"propagateCancel"))
          (Val #(interface.ok parent)))
          (Val #(interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c)))
      {{ RET #(); ctxField c ↦ (interface.ok parent : GoInterface) }}) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isClosedchanInit ∗ Pre }}
      (App (Val (@! context.withCancel)) (Val #(interface.ok parent)))
    {{ (c : Loc) (γ : ContextNames), RET #c;
        isCancelCtxOf c γ P ∗ ctxField c ↦□ (interface.ok parent : GoInterface) }}

end spec

end Perennial
