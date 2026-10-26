/-
`lock.Lock.Lock`'s spec.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.iris.dupNamespace false

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

abbrev github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock.Lock.Lock.spec : Prop :=
  ∀ (γ : LockChannelNames) (l : Lock) (R : IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg ∗ isLock γ l R }}
      (App (Val (l @!! Lock.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); R }}

end spec

end Perennial
