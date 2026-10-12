/-
`channel.mkRequest`'s spec (higher-order workers).
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

abbrev github_com.mit_pdos.perennial.goose.testdata.examples.channel.mkRequest.spec : Prop :=
  ∀ (f : GoFunc) (Q : GoString → IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg ∗
        WP (App (Val #f) (Val #())) {{ fun v => iprop(∃ s : GoString, ⌜v = #s⌝ ∗ Q s) }} }}
      (App (Val (@! mkRequest)) (Val #f))
    {{ (γfut : FutureNames) (r : request), RET #r;
        doRequest r γfut Q ∗ awaitRequest r γfut Q }}

end spec

end Perennial
