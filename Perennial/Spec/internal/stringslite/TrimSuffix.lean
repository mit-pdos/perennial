/-
`internal.stringslite.TrimSuffix`'s spec.
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

/-- `stringslite.TrimSuffix(s, suffix)`: `s` without `suffix` if it ends with it, else `s`. It
reads no package variable, so it needs no initialized package. -/
abbrev internal.stringslite.TrimSuffix.spec : Prop :=
  ∀ (s suf : GoString),
    {{ (True : IProp GF) }}
      (App (App (Val (@! TrimSuffix)) (Val #s)) (Val #suf))
    {{ RET #(if suf <:+ s then s.take (s.length - suf.length) else s); True }}

end spec

end Perennial
