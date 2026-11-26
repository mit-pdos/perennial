/-
`strings.Contains`'s spec.
-/
module

public import Perennial.Proof.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

/-- `strings.Contains(s, substr)`: whether `substr` occurs in `s` (`Index(s, substr) >= 0`). -/
abbrev strings.Contains.spec : Prop :=
  ∀ (s substr : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (App (Val (@! Contains)) (Val #s)) (Val #substr))
    {{ RET #(decide (substr <:+: s)); True }}

end spec

end Perennial
