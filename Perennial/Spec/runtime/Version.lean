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

/-- `Version()` returns the build's version, `runtime.buildVersionValue`: an opaque string, which
the linker can set to any string (`TrustedCode/runtime.lean`, `buildVersion.init`), not necessarily
valid UTF-8; a client needing more takes it as a premise about the build. -/
abbrev runtime.Version.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.runtime ∗ True }}
    (App (Val (@! Version)) (Val #()))
  {{ RET #runtime.buildVersionValue; True }}

end spec

end Perennial
