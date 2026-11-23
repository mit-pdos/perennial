/-
`crypto/fips140.Enforced`'s spec.
-/
module

public import Perennial.Proof.crypto.fips140.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.fips140.Assumptions]

/-- `Enforced()` (`enabled && !isBypassed()`) is `true` only if the `fips140` setting is
`only`. -/
abbrev crypto.fips140.Enforced.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.crypto.fips140 }}
    (App (Val (@! crypto.fips140.Enforced)) (Val #()))
  {{ (b : Bool), RET #b; ⌜b = true → godebugFips140 = go!"only"⌝ }}

end spec

end Perennial
