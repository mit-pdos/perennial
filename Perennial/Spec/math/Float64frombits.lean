/-
`math.Float64frombits`'s spec.
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

/-- `math.Float64frombits(b)`: the float whose bits are `b`, which is `b` itself (`*(*float64)(unsafe.Pointer(&b))`). -/
abbrev math.Float64frombits.spec : Prop :=
  ∀ (b : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math }}
      (App (Val (@! Float64frombits)) (Val #b))
    {{ RET #b; True }}

end spec

end Perennial
