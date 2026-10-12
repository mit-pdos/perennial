/-
`context.timerCtx.cancel`'s spec.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- `c.cancel(rm, err, cause)` for a `*timerCtx` `c` and a typed error `err`: cancels the
embedded `*cancelCtx`, removes `c` from its parent if `rm`, and stops the timer. -/
abbrev context.timerCtx.cancel.spec : Prop :=
  ∀ (c : Loc) (γ : ContextNames) (rm : Bool) (err cause : GoInterface),
    isTypedErr err →
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗
        isCancelCtxOfR (tcc c) γ iprop(True) (timerR c) ∗
        (if rm then iprop(∃ parent : GoInterfaceOk,
            ctxField (tcc c) ↦□ (interface.ok parent : GoInterface) ∗ isParentCtx parent)
         else iprop(True)) }}
      (App (App (App (Val #(methods (go.GoType.PointerType context.timerCtx.ty) go!"cancel" #c))
        (Val #rm)) (Val #err)) (Val #cause))
    {{ RET #(); ContextClosed γ }}

end spec

end Perennial
