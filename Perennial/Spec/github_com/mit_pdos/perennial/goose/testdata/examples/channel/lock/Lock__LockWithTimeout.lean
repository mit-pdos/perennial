/-
`lock.Lock.LockWithTimeout`'s spec.
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

abbrev github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock.Lock.LockWithTimeout.spec : Prop :=
  ∀ (γ : LockChannelNames) (l : Lock) (R : IProp GF) (d : time.Duration),
    {{ isPkgInit (PROP := IProp GF) pkg ∗ isLock γ l R }}
      (App (Val (l @!! Lock.ty @!! go!"LockWithTimeout")) (Val #d))
    {{ (b : Bool), RET #b; if b then R else True }}

end spec

end Perennial
