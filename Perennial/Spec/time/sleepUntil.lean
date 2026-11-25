/-
`time.sleepUntil`'s spec.
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

/-- `sleepUntil(w)`: returns (once a reading of `runtimeNano` is at least `w`). -/
abbrev time.sleepUntil.spec : Prop :=
  ∀ (w : w64),
    {{ (True : IProp GF) }}
      (App (Val (@! time.sleepUntil)) (Val #w))
    {{ RET #(); True }}

end spec

end Perennial
