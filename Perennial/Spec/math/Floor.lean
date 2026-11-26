/-
`math.Floor`'s spec.
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

/-- `math.Floor(x)`: some `float64` (`archFloor(x)` on amd64). -/
abbrev math.Floor.spec : Prop :=
  ∀ (x : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math }}
      (App (Val (@! Floor)) (Val #x))
    {{ (y : w64), RET #y; True }}

end spec

end Perennial
