/-
`math.Frexp`'s spec.
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

/-- `math.Frexp(f)`: some fraction and exponent (`frexp(f)`: no assembly on amd64). -/
abbrev math.Frexp.spec : Prop :=
  ∀ (f : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math }}
      (App (Val (@! Frexp)) (Val #f))
    {{ (fr e : w64), RET (PairV #fr #e); True }}

end spec

end Perennial
