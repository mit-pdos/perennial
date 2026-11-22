/-
`math.sqrt`'s spec.
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

/-- `math.sqrt(x)`: some `float64` (gc compiles it to the square-root instruction; its model,
`TrustedCode/math.lean`, returns an arbitrary bit pattern). -/
abbrev math.sqrt.spec : Prop :=
  ∀ (x : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math }}
      (App (Val (@! sqrt)) (Val #x))
    {{ (y : w64), RET #y; True }}

end spec

end Perennial
