/-
The proof of `lock.Lock.Unlock`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock.Lock__Unlock

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock

set_option goose.wp.extras true

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock.Lock.Unlock.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock.Lock.Unlock.spec
      (GF := GF) (hG := hG) := fun γ l R => by
  wp_start as ⟨#Hl, HR⟩
  unfold isLock
  wp_auto
  wp_apply wp_lock_channel_unlock (t := go.GoType.StructType []) γ l.ch' R $$ [$Hl $HR] as %v -
  iapply HΦ
  itrivial

end proof

end Perennial
