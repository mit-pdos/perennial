/-
`channel.Google`'s spec: Rob Pike's "Google search" example, using the future
channel idiom.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.Base
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.GoogleDefs

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
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

abbrev github_com.mit_pdos.perennial.goose.testdata.examples.channel.Google.spec : Prop :=
  ∀ (q : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! Google)) (Val #q))
    {{ (sl : GoSlice), RET #sl;
        ∃ xs : List GoString, sl ↦* xs ∗ ⌜xs.Perm (googleExpected q)⌝ }}

end spec

end Perennial
