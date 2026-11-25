/-
`sync.poolModelOf`'s spec.
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

/-- `poolModelOf(p)` returns the state of the pool `p`, a `poolModel` whose elements satisfy
`P`, installing an empty one in `p.local` if there is none yet. -/
abbrev sync.poolModelOf.spec : Prop :=
  ∀ (p : Loc) (f : GoFunc) (R : IProp GF) (P : GoAny → IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isPool p f R P }}
      (App (Val (@! poolModelOf)) (Val #p))
    {{ (s : Loc), RET #s; isPoolModel s P }}

end spec

end Perennial
