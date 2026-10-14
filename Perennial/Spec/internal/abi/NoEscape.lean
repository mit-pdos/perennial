/-
`internal.abi.NoEscape`'s spec.
-/
module

public import Perennial.Proof.internal.abi.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : internal.abi.Assumptions]

/-- `abi.NoEscape(p)` returns `p`. -/
abbrev internal.abi.NoEscape.spec : Prop :=
  ∀ (p : Loc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.abi }}
      (App (Val (@! NoEscape)) (Val #p))
    {{ RET #p; True }}

end spec

end Perennial
