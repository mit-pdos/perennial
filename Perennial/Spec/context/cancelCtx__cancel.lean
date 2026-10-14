/-
`context.cancelCtx.cancel`'s spec.
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

/-- `c.cancel(rm, err, cause)` for a typed error `err`, given `□ P`: closes `c` (and its Done
channel), cancels `c`'s children (with their stored `childCancelSpec`), and, if `rm`, removes `c`
from its parent's `children` (`removeChild(c.Context, c)`, for a parent of the kinds of
`isParentCtx`). -/
abbrev context.cancelCtx.cancel.spec : Prop :=
  ∀ (c : Loc) (γ : ContextNames) (P : IProp GF) (rm : Bool) (err cause : GoInterface),
    isTypedErr err →
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗ □ P ∗
        (if rm then iprop(∃ parent : GoInterfaceOk,
            structFieldRef context.cancelCtx go!"Context" c ↦□ (interface.ok parent : GoInterface) ∗
            isParentCtx parent)
         else iprop(True)) }}
      (App (App (App (Val #(methods (go.GoType.PointerType context.cancelCtx.ty) go!"cancel" #c))
        (Val #rm)) (Val #err)) (Val #cause))
    {{ RET #(); ContextClosed γ }}

end spec

end Perennial
