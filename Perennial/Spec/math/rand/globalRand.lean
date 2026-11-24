/-
`math/rand.globalRand`'s spec.
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

/-- `globalRand()`: the global generator, a `Rand` over the runtime's source. -/
abbrev math.rand.globalRand.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.math.rand }}
    (App (Val (@! globalRand)) (Val #()))
  {{ (r : Loc), RET #r; isRuntimeRand (GF := GF) (hG := hG) r }}

end spec

end Perennial
