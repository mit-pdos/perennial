/-
`sync.poolModelAt`'s spec.
-/
module

public import Perennial.Proof.sync.PoolDefs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- `poolModelAt(l)` (`(*poolModel)(l)`) returns `l`. It reads no package variable, so it needs
no initialized package. -/
abbrev sync.poolModelAt.spec : Prop :=
  ∀ (l : Loc),
    {{ (True : IProp GF) }}
      (App (Val (@! poolModelAt)) (Val #l))
    {{ RET #l; True }}

end spec

end Perennial
