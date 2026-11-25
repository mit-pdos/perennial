/-
`time.when`'s spec.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- `when(d)`: some positive `int64` (a timer's deadline: `runtimeNano() + d`, saturated). -/
abbrev time.when.spec : Prop :=
  ∀ (d : time.Duration),
    {{ (True : IProp GF) }}
      (App (Val (@! time.when)) (Val #d))
    {{ (x : w64), RET #x; ⌜0 < sint.Z x⌝ }}

end spec

end Perennial
