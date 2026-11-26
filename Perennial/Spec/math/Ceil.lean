/-
`math.Ceil`'s spec.
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

/-- `math.Ceil(x)`: some `float64` (`archCeil(x)` on amd64). -/
abbrev math.Ceil.spec : Prop :=
  ∀ (x : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math }}
      (App (Val (@! Ceil)) (Val #x))
    {{ (y : w64), RET #y; True }}

end spec

end Perennial
