/-
`time.runtimeNano`'s spec.
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

/-- `runtimeNano()` (the runtime's monotonic clock; its Go model reads the primitive stub `now`):
some positive `int64` (Go's readings are positive: `when` and the runtime's timers rely on it). -/
abbrev time.runtimeNano.spec : Prop :=
    {{ (True : IProp GF) }}
      (App (Val (@! time.runtimeNano)) (Val #()))
    {{ (x : w64), RET #x; ⌜0 < sint.Z x⌝ }}

end spec

end Perennial
