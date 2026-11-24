/-
`internal.gomodel.Choose`'s spec.
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

/-- `gomodel.Choose()`: some boolean. It reads no package variable, so it needs no initialized
package. -/
abbrev internal.gomodel.Choose.spec : Prop :=
    {{ (True : IProp GF) }}
      (App (Val (@! internal.gomodel.Choose)) (Val #()))
    {{ (b : Bool), RET #b; True }}

end spec

end Perennial
