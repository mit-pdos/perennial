/-
`runtime.Version`'s spec.
-/
module

public import Perennial.Proof.runtime.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : runtime.Assumptions]

/-- `Version()` returns some string: the build's version, which the linker sets to any string
(its Go model, `goose/model/overlay/runtime`), not necessarily valid UTF-8. -/
abbrev runtime.Version.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.runtime ∗ True }}
    (App (Val (@! Version)) (Val #()))
  {{ (v : GoString), RET #v; True }}

end spec

end Perennial
