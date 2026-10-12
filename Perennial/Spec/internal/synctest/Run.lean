/-
`internal.synctest.Run`'s spec.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.synctest.Assumptions]

/-- `synctest.Run` is not supported by Perennial; it changes the semantics of go
programs because it messes with runtime state (i.e. it creates a new bubble). -/
abbrev internal.synctest.Run.spec : Prop :=
  ∀ (v : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.internal.synctest ∗ False }}
    (App (Val (@! Run)) (Val #v))
  {{ RET #(); True }}

end spec

end Perennial
