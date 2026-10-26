/-
The proof of `lock.NewLock`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock.NewLock

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock.NewLock.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock.NewLock.spec
      (GF := GF) (hG := hG) := fun R => by
  wp_start as HR
  wp_auto
  iapply wp_fupd
  wp_apply chan.wp_make2 (V := Unit) $$ [] as %ch %γch ⟨#Hchan, %Hcap, Hoc⟩
  · ipureintro; decide
  imod start_lock_channel (V := Unit) ch R γch Hcap $$ Hchan Hoc HR with ⟨%γlock, #Hislock⟩
  imodintro
  iapply HΦ
  unfold isLock
  iexact Hislock

end proof

end Perennial
