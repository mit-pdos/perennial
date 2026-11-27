/-
`math.chooseNaN`'s spec.
-/
module

public import Perennial.Proof.math.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.Assumptions]

/-- `math.chooseNaN()` (a declaration of the Go model, `goose/model/overlay/math`): some
`float64`. -/
abbrev math.chooseNaN.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.math }}
    (App (Val (@! chooseNaN)) (Val #()))
  {{ (y : w64), RET #y; True }}

end spec

end Perennial
