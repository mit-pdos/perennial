/-
`etcd_session.newSession`'s spec.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session.Base

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
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session

abbrev github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session.newSession.spec : Prop :=
    {{ (True : IProp GF) }}
      (App (Val (@! newSession)) (Val #()))
    {{ (err : GoError), RET #err; True }}

end spec

end Perennial
