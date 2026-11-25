/-
`math/rand.seedrand`'s spec.
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

/-- `seedrand(x)`: returns (wrapping `int32` arithmetic; its divisions are by a nonzero constant). -/
abbrev math.rand.seedrand.spec : Prop :=
  ∀ (x : w32),
    {{ (True : IProp GF) }}
      (App (Val (@! seedrand)) (Val #x))
    {{ (y : w32), RET #y; True }}

end spec

end Perennial
