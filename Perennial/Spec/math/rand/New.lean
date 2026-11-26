/-
`math/rand.New`'s spec.
-/
module

public import Perennial.Proof.math.rand.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.rand.Assumptions]

/-- `New(src)`, for any `src`: a fresh `*Rand` over `src`, never written afterwards (only `Seed` and
`Read` write a `Rand`; neither is translated), so its points-to is persistent. Its `s64` is `src` or
`nil` (the comma-ok assertion `src.(Source64)`), which this spec leaves open. -/
abbrev math.rand.New.spec : Prop :=
  ∀ (src : GoInterface),
    {{ (True : IProp GF) }}
      (App (Val (@! New)) (Val #src))
    {{ (r : Loc), RET #r; ∃ v : Rand, r ↦□ v ∗ ⌜v.src' = src⌝ }}

end spec

end Perennial
