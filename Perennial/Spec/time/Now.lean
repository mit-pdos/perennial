/-
`time.Now`'s spec.
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

/-- Spec of `time.Now` (axiom). -/
abbrev time.Now.spec : Prop :=
    {{ (True : IProp GF) }}
      (App (Val (@! time.Now)) (Val #()))
    {{ (t : time.Time), RET #t; True }}

end spec

end Perennial
