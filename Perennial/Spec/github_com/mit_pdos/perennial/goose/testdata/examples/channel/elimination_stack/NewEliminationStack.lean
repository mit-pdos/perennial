/-
`elimination_stack.NewEliminationStack`'s spec.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack

abbrev github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.NewEliminationStack.spec : Prop :=
  ∀ (N : Namespace),
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! NewEliminationStack)) (Val #()))
    {{ (s : Loc) (γ : EliminationStackNames), RET #s;
        isEliminationStack s γ N ∗ ownEliminationStack γ [] }}

end spec

end Perennial
