/-
`context.Cause`'s spec.
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

abbrev context.Cause.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (ctx_desc : ContextDesc (IProp GF)),
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗
        "#Hctx" ∷ isContext ctx ctx_desc }}
      (App (Val (@! context.Cause)) (Val #(interface.ok ctx)))
    {{ (err : GoInterface), RET #err; True }}

end spec

end Perennial
