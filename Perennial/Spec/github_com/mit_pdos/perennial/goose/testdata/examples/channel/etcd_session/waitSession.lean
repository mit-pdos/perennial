/-
`etcd_session.waitSession`'s spec.
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

/-- Spec of the `waitSession` function. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session.waitSession.spec : Prop :=
  ∀ {A' : Type} [ZeroVal A'] [TypedPointsto (GF := GF) A'] [Pos.Countable A'] {A : go.GoType}
    [IntoValTyped (GF := GF) A' A] (cancel : Loc) (γcancel : ChanNames) (Pcancel : A' → IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg ∗ isChanBag γcancel cancel Pcancel }}
      (App (Val #(functions waitSession [A])) (Val #cancel))
    {{ (err : GoError), RET #err;
        match err with
        | GoInterface.nil => iprop(True)
        | _ => iprop(∃ a, Pcancel a) }}

end spec

end Perennial
