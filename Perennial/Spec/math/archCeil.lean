/-
`math.archCeil`'s spec.
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

/-- `math.archCeil(x)`: some `float64` (its Go model, `goose/model/overlay/math`: Go's portable
`ceil(x)`, or some NaN for a NaN). -/
abbrev math.archCeil.spec : Prop :=
  ∀ (x : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math }}
      (App (Val (@! archCeil)) (Val #x))
    {{ (y : w64), RET #y; True }}

end spec

end Perennial
