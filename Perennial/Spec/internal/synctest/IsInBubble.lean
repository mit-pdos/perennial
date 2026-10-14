/-
`internal.synctest.IsInBubble`'s spec.
-/
module

public import Perennial.Proof.internal.synctest.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : internal.synctest.Assumptions]

/-- `synctest.IsInBubble` always returns false since Perennial doesn't permit
`synctest.Run`. -/
abbrev internal.synctest.IsInBubble.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.internal.synctest }}
    (App (Val (@! IsInBubble)) (Val #()))
  {{ RET #false; True }}

end spec

end Perennial
