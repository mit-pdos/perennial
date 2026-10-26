/-
`lock.NewLock`'s spec.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock.Base

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
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock

abbrev github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock.NewLock.spec : Prop :=
  ∀ (R : IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg ∗ ▷ R }}
      (App (Val (@! NewLock)) (Val #()))
    {{ (γ : LockChannelNames) (l : Lock), RET #l; isLock γ l R }}

end spec

end Perennial
