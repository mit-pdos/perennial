/-
`internal.bytealg.IndexRabinKarp`'s spec.
-/
module

public import Perennial.Proof.internal.bytealg.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

/-- `bytealg.IndexRabinKarp[string](s, sep)`: the first index of `sep` in `s`, or `-1`, for a
`sep` no longer than `s` (its first loop reads `s[i]` for `i < len(sep)`). Only the instance at
`string` (the one `stringslite.Index` calls). -/
abbrev internal.bytealg.IndexRabinKarp.spec : Prop :=
  ∀ (s sep : GoString),
    {{ (⌜sep.length ≤ s.length⌝ : IProp GF) }}
      (App (App (Val #(functions internal.bytealg.IndexRabinKarp [go.string])) (Val #s))
        (Val #sep))
    {{ RET #(W64 (internal.bytealg.index s sep)); True }}

end spec

end Perennial
