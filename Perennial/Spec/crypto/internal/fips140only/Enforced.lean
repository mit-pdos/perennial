/-
`crypto/internal/fips140only.Enforced`'s spec.
-/
module

public import Perennial.Proof.crypto.internal.fips140only.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.internal.fips140only.Assumptions]

/-- `Enforced()` is `fips140.Enforced()`: `true` only if the `fips140` setting is `only`. -/
abbrev crypto.internal.fips140only.Enforced.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.crypto.internal.fips140only }}
    (App (Val (@! crypto.internal.fips140only.Enforced)) (Val #()))
  {{ (b : Bool), RET #b; ⌜b = true → crypto.fips140.godebugFips140 = go!"only"⌝ }}

end spec

end Perennial
