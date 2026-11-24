/-
`time.nextWhen`'s spec.
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

/-- `nextWhen(when, period)`: some `int64` (a periodic timer's next deadline). -/
abbrev time.nextWhen.spec : Prop :=
  ∀ (w p : w64),
    {{ (True : IProp GF) }}
      (App (App (Val (@! time.nextWhen)) (Val #w)) (Val #p))
    {{ (x : w64), RET #x; True }}

end spec

end Perennial
