/-
`context.cancelCtx.Err`'s spec.
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

abbrev context.cancelCtx.Err.spec : Prop :=
  ∀ (c : Loc) (γ : ContextNames) (P : IProp GF) (cl : Bool),
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P ∗
        (if cl then ContextClosed γ else iprop(True)) }}
      (App (Val #(methods (go.GoType.PointerType context.cancelCtx.ty) go!"Err" #c)) (Val #()))
    {{ (e : GoInterface), RET #e; ⌜cl = true → e ≠ interface.nil⌝ ∗
        (if e = interface.nil then iprop(True)
         else iprop(⌜isTypedErr e⌝ ∗ □ P ∗ ContextClosed γ)) }}

end spec

end Perennial
