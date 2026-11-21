/-
`internal.sync.initialize'`'s spec.
-/
module

public import Perennial.Proof.internal.sync.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.sync.Assumptions]

abbrev internal.sync.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.internal.sync get_is_pkg_init →
  {{ ownInitializing get_is_pkg_init }}
    (App (Val initialize') (Val #()))
  {{ RET #(); ownInitializing get_is_pkg_init ∗
      isPkgInit (PROP := IProp GF) pkg_id.internal.sync }}

end spec

end Perennial
