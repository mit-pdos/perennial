/-
The proof of `lock.Lock.LockWithTimeout`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock.Lock__LockWithTimeout
public import Perennial.Spec.time.After

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock.Lock.LockWithTimeout.wp_proof
    (wp_After : time.After.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock.Lock.LockWithTimeout.spec
      (GF := GF) (hG := hG) := fun γ l R d => by
  wp_start as #Hl
  unfold isLock
  wp_auto
  wp_apply +noauto wp_After
  iintro %after_ch %γafter #Hafter
  wp_auto_lc 2
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, l.ch', γ.lchanName, ()
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · iapply isLockChannel_is_chan $$ Hl
    iapply lock_channel_send_au $$ Hl Hlc1
    inext
    iintro HR
    wp_auto
    iapply HΦ $$ %true
    simp only [↓reduceIte]
    iexact HR
  iapply BigAndL.bigAndL_singleton.2
  simp only [chan.blockingClausePre]
  iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, after_ch, γafter
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply is_bag_is_chan $$ Hafter
  iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hafter
  inext
  iintro %t -
  wp_auto
  iapply HΦ
  simp only [Bool.false_eq_true, ↓reduceIte]
  itrivial

end proof

end Perennial
