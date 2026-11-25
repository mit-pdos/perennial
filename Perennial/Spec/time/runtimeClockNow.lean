/-
`time.runtimeClockNow`'s spec.
-/
module

public import Perennial.Proof.time.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- `runtimeClockNow()`: a reading `x` of the model's runtime clock (`clockLb`), positive and at
least any bound `n` the caller holds (`n` counted as `clockMax` above it, `clockEnc`). -/
abbrev time.runtimeClockNow.spec : Prop :=
  ∀ (n : Int),
    {{ time.clockLb (GF := GF) n }}
      (App (Val (@! time.runtimeClockNow)) (Val #()))
    {{ (x : w64), RET #x; ⌜time.clockEnc n ≤ time.clockEnc (sint.Z x)⌝ ∗ ⌜0 < sint.Z x⌝ ∗
        time.clockLb (sint.Z x) }}

end spec

end Perennial
