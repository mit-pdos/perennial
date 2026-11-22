/-
`math.IsInf`'s spec.
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

/-- `math.IsInf(f, sign)`: whether `f` (`|f|` if `sign = 0`, `-f` if `sign < 0`) is greater than
`MaxFloat64`. -/
abbrev math.IsInf.spec : Prop :=
  ∀ (f sign : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math }}
      (App (App (Val (@! IsInf)) (Val #f)) (Val #sign))
    {{ (b : Bool), RET #b; True }}

end spec

end Perennial
