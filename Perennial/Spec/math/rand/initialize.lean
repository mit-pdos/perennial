/-
`math/rand.initialize'`'s spec.
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

/-- The package's `initialize'`: it establishes `math/rand`'s `isPkgInit`, the invariant of the
global generator (`isInit`). -/
abbrev math.rand.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.math.rand get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.math.rand }}

end spec

end Perennial
