/-
`math.IsNaN`'s spec.
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

/-- `math.IsNaN(f)`: whether `f` is a NaN (`f != f`). -/
abbrev math.IsNaN.spec : Prop :=
  ∀ (f : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math }}
      (App (Val (@! IsNaN)) (Val #f))
    {{ RET #(float64IsNaN f); True }}

end spec

end Perennial
