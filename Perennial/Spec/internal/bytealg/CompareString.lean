/-
`internal.bytealg.CompareString`'s spec.
-/
module

public import Perennial.Proof.internal.bytealg.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

/-- `bytealg.CompareString(a, b)`: `compareResult a b`. -/
abbrev internal.bytealg.CompareString.spec : Prop :=
  ∀ (a b : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.bytealg }}
      (App (App (Val (@! CompareString)) (Val #a)) (Val #b))
    {{ RET #(compareResult a b); True }}

end spec

end Perennial
