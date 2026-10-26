/-
`context.cancelCtx.Done`'s spec.
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

abbrev context.cancelCtx.Done.spec : Prop :=
  ∀ (c : Loc) (γ : ContextNames) (P : IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOf c γ P }}
      (App (Val #(methods (go.GoType.PointerType context.cancelCtx.ty) go!"Done" #c)) (Val #()))
    {{ (ch : GoChan) (γch : ChanNames), RET #ch; isContextDone (cdesc γ P) ch γch ∗
        doneFresh γ P ch }}

end spec

end Perennial
