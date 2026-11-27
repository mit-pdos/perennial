/-
`time.runtimeClockWaitUntil`'s spec.
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

/-- `runtimeClockWaitUntil(w)`: a reading `x ≥ w` of the model's runtime clock (`clockLb`). -/
abbrev time.runtimeClockWaitUntil.spec : Prop :=
  ∀ (n : Int) (w : w64),
    {{ time.clockLb (GF := GF) n }}
      (App (Val (@! time.runtimeClockWaitUntil)) (Val #w))
    {{ (x : w64), RET #x; ⌜sint.Z w ≤ sint.Z x⌝ ∗ time.clockLb (sint.Z x) }}

end spec

end Perennial
