/-
The proof of `channel.HelloWorldCancellable`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.HelloWorldCancellable
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.HelloWorldAsync

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
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

set_option goose.wp.extras true

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.HelloWorldCancellable.wp_proof
    (wp_HelloWorldAsync :
      github_com.mit_pdos.perennial.goose.testdata.examples.channel.HelloWorldAsync.spec
        (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.HelloWorldCancellable.spec
      (GF := GF) (hG := hG) := fun done_ch err_ptr1 err_msg γdone => by
  wp_start as #Hdone_bc
  ihave #Hdone_chan := ownBroadcastChan_is_chan _ _ _ _ $$ Hdone_bc
  wp_pures
  wp_alloc l as Hl
  wp_pures
  wp_alloc d as Hd
  wp_auto
  wp_apply +noauto wp_HelloWorldAsync
  iintro %ch %γfut ⟨#Hch, #Hfut⟩
  wp_auto_lc 2
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · dsimp only [chan.blockingClausePre]
    iexists GoString, inferInstance, inferInstance, inferInstance, inferInstance, ch, γfut
    isplitr
    · ipureintro; rfl
    iframe Hch
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hfut
    inext
    iintro %v %Hv
    subst Hv
    wp_auto
    iapply HΦ
    ipureintro; exact .inr rfl
  iapply BigAndL.bigAndL_cons.2
  isplit
  · dsimp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, done_ch, γdone
    isplitr
    · ipureintro; rfl
    iframe Hdone_chan
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hdone_bc
    iintro ⟨#Herr, -⟩
    wp_auto
    iapply HΦ
    ipureintro; exact .inl rfl
  · iapply BigAndL.bigAndL_nil.2
    itrivial

end proof

end Perennial
