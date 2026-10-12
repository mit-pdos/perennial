/-
`context.Background`'s spec.
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

/-- `Background()` returns `backgroundCtxVal`. -/
abbrev context.Background.spec : Prop :=
    {{ (True : IProp GF) }}
      (App (Val (@! context.Background)) (Val #()))
    {{ RET #(interface.ok backgroundCtxVal); True }}

end spec

end Perennial
