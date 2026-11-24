/-
`time.now`'s spec.
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

/-- `now()`, a primitive stub of the model (`TrustedCode/time.lean`; the runtime's `time_now`: the
wall clock and the monotonic clock): some `(sec, nsec, mono)` of its result types. -/
abbrev time.now.spec : Prop :=
    {{ (True : IProp GF) }}
      (App (Val (@! time.now)) (Val #()))
    {{ (sec : w64) (nsec : w32) (mono : w64), RET (PairV (PairV #sec #nsec) #mono); True }}

end spec

end Perennial
