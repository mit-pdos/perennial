/-
`internal.race.initialize'`'s spec.
-/
module

public import Perennial.Proof.internal.race.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : internal.race.Assumptions]

abbrev internal.race.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.internal.race get_is_pkg_init →
  {{ ownInitializing get_is_pkg_init }}
    (App (Val initialize') (Val #()))
  {{ RET #(); ownInitializing get_is_pkg_init ∗
      isPkgInit (PROP := IProp GF) pkg_id.internal.race }}

end spec

end Perennial
