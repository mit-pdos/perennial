/-
`etcd_session.monitorSession`'s spec.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session.Base

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
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session

abbrev github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session.monitorSession.spec : Prop :=
  ∀ (ch : GoChan) (γch : ChanNames),
    {{ isPkgInit (PROP := IProp GF) pkg ∗
        "sessionc" ∷ typedPointsto (globalAddr sessionc) ch (DFrac.own (1 : Qp).half) ∗
        "Hsessionc" ∷ ownBroadcastChan ch γch iprop(True) Broadcast.Pending ∗
        "#Hsessionc_is" ∷ isChan ch γch Unit }}
      (App (Val (@! monitorSession)) (Val #()))
    {{ RET #(); True }}

end spec

end Perennial
