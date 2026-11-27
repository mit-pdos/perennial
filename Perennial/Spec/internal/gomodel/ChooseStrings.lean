/-
`internal.gomodel.ChooseStrings`'s spec.
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

/-- `gomodel.ChooseStrings()` returns some slice of strings, owned with its capacity. It reads no
package variable, so it needs no initialized package. -/
abbrev internal.gomodel.ChooseStrings.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! internal.gomodel.ChooseStrings)) (Val #()))
  {{ (s : GoSlice), RET #s; ∃ xs : List GoString,
        s ↦* xs ∗ ownSliceCap GoString s (DFrac.own 1) }}

end spec

end Perennial
