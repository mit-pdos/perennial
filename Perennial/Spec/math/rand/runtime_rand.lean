/-
`math/rand.runtime_rand`'s spec.
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

/-- `runtime_rand()`: some `uint64` (the runtime's `rand`, a trusted model). -/
abbrev math.rand.runtime_rand.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! runtime_rand)) (Val #()))
  {{ (x : w64), RET #x; True }}

end spec

end Perennial
