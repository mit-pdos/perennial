/-
`runtime.Callers`'s spec.
-/
module

public import Perennial.Proof.runtime.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : runtime.Assumptions]

/-- `Callers(skip, pc)` fills some prefix of `pc` with program counters and returns its length
(arbitrary words: the model does not know the stack), below `2^40`: a stack has fewer frames
(`TrustedCode/runtime.lean`, `callers.impl`), so a buffer of `2^40` or more is never filled. -/
abbrev runtime.Callers.spec : Prop :=
  ∀ (skip : w64) (s : GoSlice) (xs : List w64),
    {{ (s ↦* xs : IProp GF) }}
      (App (App (Val (@! Callers)) (Val #skip)) (Val #s))
    {{ (n : w64), RET #n; ∃ ys : List w64,
        ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ xs.length ∧ sint.Z n < 2 ^ 40 ∧ ys.length = xs.length ∧
          ys.drop (sint.nat n) = xs.drop (sint.nat n)⌝ ∗ s ↦* ys }}

end spec

end Perennial
