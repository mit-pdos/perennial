/-
`context.removeChild`'s spec.
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

/-- `removeChild(parent, child)` for a child (a `canceler`) that is a safe map key. -/
abbrev context.removeChild.spec : Prop :=
  ∀ (parent : GoInterfaceOk) (child : GoInterface)
      [SafeMapKey (GF := GF) context.canceler.ty child],
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isParentCtx parent }}
      (App (App (Val (@! context.removeChild)) (Val #(interface.ok parent))) (Val #child))
    {{ RET #(); True }}

end spec

end Perennial
