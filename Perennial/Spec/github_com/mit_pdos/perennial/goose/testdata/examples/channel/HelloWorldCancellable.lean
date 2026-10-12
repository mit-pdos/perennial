/-
`channel.HelloWorldCancellable`'s spec (cancellation).
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.Base

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

abbrev github_com.mit_pdos.perennial.goose.testdata.examples.channel.HelloWorldCancellable.spec : Prop :=
  ∀ (done_ch : GoChan) (err_ptr1 : Loc) (err_msg : GoString) (γdone : ChanNames),
    {{ isPkgInit (PROP := IProp GF) pkg ∗
        ownBroadcastChan done_ch γdone iprop(err_ptr1 ↦□ err_msg) .Unknown }}
      (App (App (Val (@! HelloWorldCancellable)) (Val #done_ch)) (Val #err_ptr1))
    {{ (result : GoString), RET #result;
        ⌜result = err_msg ∨ result = go!"Hello, World!"⌝ }}

end spec

end Perennial
