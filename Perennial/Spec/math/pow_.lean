/-
`math.pow`'s spec.
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

/-- `math.pow(x, y)`: some `float64` (no panic). -/
abbrev math.pow.spec : Prop :=
  ∀ (x y : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math }}
      (App (App (Val (@! pow)) (Val #x)) (Val #y))
    {{ (r : w64), RET #r; True }}

end spec

end Perennial
