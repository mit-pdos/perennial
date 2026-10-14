/-
`strings.Compare`'s spec.
-/
module

public import Perennial.Proof.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

/-- `strings.Compare(a, b)`: `-1`, `0` or `+1` as `a` is lexicographically less than, equal to
or greater than `b`. -/
abbrev strings.Compare.spec : Prop :=
  ∀ (a b : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (App (Val (@! Compare)) (Val #a)) (Val #b))
    {{ RET #(compareResult a b); True }}

end spec

end Perennial
