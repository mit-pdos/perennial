/-
`context.TODO`'s spec.
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

/-- `TODO()` returns `todoCtxVal`. -/
abbrev context.TODO.spec : Prop :=
    {{ (True : IProp GF) }}
      (App (Val (@! context.TODO)) (Val #()))
    {{ RET #(interface.ok todoCtxVal); True }}

end spec

end Perennial
