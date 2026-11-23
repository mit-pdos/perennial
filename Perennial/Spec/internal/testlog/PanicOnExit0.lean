/-
`internal.testlog.PanicOnExit0`'s spec.
-/
module

public import Perennial.Proof.internal.testlog.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.testlog.Assumptions]

/-- `PanicOnExit0()` returns false: the flag is false for good under the package's fact. -/
abbrev internal.testlog.PanicOnExit0.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.internal.testlog }}
    (App (Val (@! PanicOnExit0)) (Val #()))
  {{ RET #false; True }}

end spec

end Perennial
