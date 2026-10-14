/-
`sync.(*Once).Do`'s spec.
-/
module

public import Perennial.Proof.sync.OnceDefs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

abbrev sync.Once.Do.spec : Prop :=
  ∀ (o : Loc) (P Q : IProp GF) (f : GoFunc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isOnce o P Q ∗
        iprop({{ P }} (App (Val #f) (Val #())) {{ RET #(); Q }}) }}
      (App (Val (o @!! go.GoType.PointerType Once.ty @!! go!"Do")) (Val #f))
    {{ RET #(); Q }}

end spec

end Perennial
