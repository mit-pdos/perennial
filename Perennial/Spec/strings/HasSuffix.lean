/-
`strings.HasSuffix`'s spec.
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

/-- `strings.HasSuffix(s, suffix)`: whether `s` ends with `suffix`. It reads no package
variable, so it needs no initialized package. -/
abbrev strings.HasSuffix.spec : Prop :=
  ∀ (s suf : GoString),
    {{ (True : IProp GF) }}
      (App (App (Val (@! HasSuffix)) (Val #s)) (Val #suf))
    {{ RET #(decide (suf <:+ s)); True }}

end spec

end Perennial
