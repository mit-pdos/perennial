/-
`internal.gomodel.ChooseString`'s spec.
-/
module

public import Perennial.Proof.internal.gomodel.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.gomodel.Assumptions]

/-- `gomodel.ChooseString()` returns some string. It reads no package variable, so it needs no
initialized package. -/
abbrev internal.gomodel.ChooseString.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! internal.gomodel.ChooseString)) (Val #()))
  {{ (s : GoString), RET #s; True }}

end spec

end Perennial
