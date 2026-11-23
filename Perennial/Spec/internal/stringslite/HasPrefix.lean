/-
`internal.stringslite.HasPrefix`'s spec.
-/
module

public import Perennial.Proof.internal.stringslite.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.stringslite.Assumptions]

/-- `stringslite.HasPrefix(s, prefix)`: whether `s` begins with `prefix`. It reads no package
variable, so it needs no initialized package. -/
abbrev internal.stringslite.HasPrefix.spec : Prop :=
  ∀ (s pre : GoString),
    {{ (True : IProp GF) }}
      (App (App (Val (@! HasPrefix)) (Val #s)) (Val #pre))
    {{ RET #(decide (pre <+: s)); True }}

end spec

end Perennial
