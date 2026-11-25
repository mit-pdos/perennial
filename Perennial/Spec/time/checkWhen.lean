/-
`time.checkWhen`'s spec.
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

/-- `checkWhen(when, period)`: returns for a positive `when` and a non-negative `period` (the
model is stuck otherwise, where the runtime's `timer.modify` throws). -/
abbrev time.checkWhen.spec : Prop :=
  ∀ (w p : w64),
    {{ (⌜0 < sint.Z w ∧ 0 ≤ sint.Z p⌝ : IProp GF) }}
      (App (App (Val (@! time.checkWhen)) (Val #w)) (Val #p))
    {{ RET #(); True }}

end spec

end Perennial
