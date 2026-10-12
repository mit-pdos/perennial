/-
`context.cancelCtx.Value`'s spec.
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

abbrev context.cancelCtx.Value.spec : Prop :=
  ∀ (c : Loc) (γ : ContextNames) (P : IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P }}
      (App (Val #(methods (go.GoType.PointerType context.cancelCtx.ty) go!"Value" #c))
        (Val #cancelCtxKeyAny))
    {{ RET #(interface.mkOk (go.GoType.PointerType context.cancelCtx.ty) #c); True }}

end spec

end Perennial
