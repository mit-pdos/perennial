/-
`workq.(*Worker).run`'s spec.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.Base

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
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq

abbrev github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.Worker.run.spec : Prop :=
  ∀ (γ : WorkqNames) (w neighbor : Loc) (sh : shared),
    {{ isPkgInit (PROP := IProp GF) pkg ∗
        "#Hw" ∷ isWorker γ w ∗
        "#Hneighbor" ∷ isWorker γ neighbor ∗
        "#Hcoord" ∷ isCoordinator γ sh }}
      (App (App (Val (w @!! go.GoType.PointerType Worker.ty @!! go!"run")) (Val #neighbor)) (Val #sh))
    {{ RET #(); True }}

end spec

end Perennial
