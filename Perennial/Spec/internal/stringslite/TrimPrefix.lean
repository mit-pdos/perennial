/-
`internal.stringslite.TrimPrefix`'s spec.
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

/-- `stringslite.TrimPrefix(s, prefix)`: `s` without `prefix` if it begins with it, else `s`. It
reads no package variable, so it needs no initialized package. -/
abbrev internal.stringslite.TrimPrefix.spec : Prop :=
  ∀ (s pre : GoString),
    {{ (True : IProp GF) }}
      (App (App (Val (@! TrimPrefix)) (Val #s)) (Val #pre))
    {{ RET #(if pre <+: s then s.drop pre.length else s); True }}

end spec

end Perennial
