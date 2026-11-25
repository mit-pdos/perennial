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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- `c.Err()` for a `*cancelCtx` with allowed errors `A` (`isCancelCtxOfA`): `nil`, or (always,
given `ContextClosed γ`) a typed error that is `Canceled`'s or `DeadlineExceeded`'s value
(`isCtxErr`), one `A` allows, with `□ P` and `ContextClosed γ`. -/
abbrev context.cancelCtx.Err.spec : Prop :=
  ∀ (c : Loc) (γ : ContextNames) (P : IProp GF) (A : GoInterface → Prop) (cl : Bool),
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isCancelCtxOfA c γ P A ∗
        (if cl then ContextClosed γ else iprop(True)) }}
      (App (Val #(methods (go.GoType.PointerType context.cancelCtx.ty) go!"Err" #c)) (Val #()))
    {{ (e : GoInterface), RET #e; ⌜cl = true → e ≠ interface.nil⌝ ∗
        (if e = interface.nil then iprop(True)
         else iprop(⌜isTypedErr e⌝ ∗ isCtxErr e ∗ □ P ∗ ContextClosed γ ∗ ⌜A e⌝)) }}

end spec

end Perennial
