/-
`fmt.initialize'`'s spec.
-/
module

public import Perennial.Proof.fmt.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

/-- The package's `initialize'`: allocate the package's variables, after initializing `sync`,
`io` and `errors`. -/
abbrev fmt.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.fmt get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.fmt }}

end spec

end Perennial
