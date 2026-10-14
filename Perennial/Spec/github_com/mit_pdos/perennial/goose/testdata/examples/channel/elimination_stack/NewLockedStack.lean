/-
`elimination_stack.NewLockedStack`'s spec.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.Base

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
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack

abbrev github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.NewLockedStack.spec : Prop :=
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! NewLockedStack)) (Val #()))
    {{ (s : Loc) (γ : GName), RET #s; isLockedStack s γ ∗ ownLockedStack γ [] }}

end spec

end Perennial
