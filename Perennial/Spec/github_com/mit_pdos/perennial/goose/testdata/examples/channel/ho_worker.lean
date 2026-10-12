/-
`channel.ho_worker`'s spec: a worker goroutine runs the closures received over a
channel and sends each result back over the request's future channel.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.Base
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.HigherOrderDefs

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
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

abbrev github_com.mit_pdos.perennial.goose.testdata.examples.channel.ho_worker.spec : Prop :=
  ∀ (γ : ChanNames) (ch : Loc),
    {{ isPkgInit (PROP := IProp GF) pkg ∗ isRequestChan γ ch }}
      (App (Val (@! ho_worker)) (Val #ch))
    {{ RET #(); True }}

end spec

end Perennial
