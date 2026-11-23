/-
`math.NaN`'s spec.
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

/-- `math.NaN()`: the NaN whose bits are `uvnan` (`0x7FF8000000000001`). -/
abbrev math.NaN.spec : Prop :=
    {{ isPkgInit (PROP := IProp GF) pkg_id.math }}
      (App (Val (@! NaN)) (Val #()))
    {{ RET #(W64 0x7FF8000000000001); True }}

end spec

end Perennial
