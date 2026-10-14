/-
`channel.HelloWorldWithTimeout`'s spec (cancellation).
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

abbrev github_com.mit_pdos.perennial.goose.testdata.examples.channel.HelloWorldWithTimeout.spec : Prop :=
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! HelloWorldWithTimeout)) (Val #()))
    {{ (result : GoString), RET #result;
        ⌜result = go!"Hello, World!" ∨ result = go!"operation timed out"⌝ }}

end spec

end Perennial
