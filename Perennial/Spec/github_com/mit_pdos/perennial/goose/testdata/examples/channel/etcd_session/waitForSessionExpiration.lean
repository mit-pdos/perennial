/-
`etcd_session.waitForSessionExpiration`'s spec.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session

abbrev github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session.waitForSessionExpiration.spec : Prop :=
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! waitForSessionExpiration)) (Val #()))
    {{ RET #(); True }}

end spec

end Perennial
