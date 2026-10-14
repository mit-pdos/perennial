/-
`crypto/rand.initialize'`'s spec.
-/
module

public import Perennial.Proof.crypto.rand.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.rand.Assumptions]

/-- The package's `initialize'`: it establishes `crypto/rand`'s `isPkgInit`, the package's
`Reader` (`isInitialized`). -/
abbrev crypto.rand.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.crypto.rand get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.crypto.rand }}

end spec

end Perennial
