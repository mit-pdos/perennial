/-
`math.Ldexp`'s spec.
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

/-- `math.Ldexp(frac, exp)`: some `float64` (`ldexp`: no assembly on amd64). -/
abbrev math.Ldexp.spec : Prop :=
  ∀ (frac exp : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math }}
      (App (App (Val (@! Ldexp)) (Val #frac)) (Val #exp))
    {{ (y : w64), RET #y; True }}

end spec

end Perennial
