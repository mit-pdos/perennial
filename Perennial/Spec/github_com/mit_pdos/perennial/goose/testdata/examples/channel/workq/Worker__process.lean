/-
`workq.(*Worker).process`'s spec.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq

abbrev github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.Worker.process.spec : Prop :=
  ∀ (γ : WorkqNames) (w : Loc) (doc : GoString) (sh : shared),
    {{ isPkgInit (PROP := IProp GF) pkg ∗
        "#Hw" ∷ isWorker γ w ∗
        "#Hcoord" ∷ isCoordinator γ sh ∗
        "Hdoc" ∷ ownTask γ doc }}
      (App (App (Val (w @!! go.GoType.PointerType Worker.ty @!! go!"process")) (Val #doc)) (Val #sh))
    {{ RET #(); True }}

end spec

end Perennial
