/-
The proof of `workq.(*Worker).run`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.Worker__run
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.Worker__process

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
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq

set_option goose.wp.extras true

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.Worker.run.wp_proof
    (wp_Worker_process :
      github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.Worker.process.spec
        (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.Worker.run.spec
      (GF := GF) (hG := hG) := fun γ w neighbor sh => by
  wp_start as ⟨#Hw, #Hneighbor, #Hcoord⟩
  iNamed Hw
  iNamed Hneighbor
  iNamed Hcoord
  ihave #Hcoord2 := Hcoord
  iNamed Hcoord2
  ihave #Hn2 := Hneighbor
  iunfold isWorker at Hn2
  icases Hn2 with ⟨%nv, %γsteal_n, %γqueue_n, #Hnpt, #Hqueue_n, #Hsteal_n⟩
  wp_auto
  wp_for
  ihave #Hw2 := Hw
  iunfold isWorker at Hw2
  icases Hw2 with ⟨%wv, %γsteal, %γqueue, #Hwpt, #Hqueue, #Hsteal⟩
  icases Hwpt with ∗Hwpt
  iStructNamed Hwpt
  wp_auto_lc 2
  wp_apply_core chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_cons.2
    isplit
    · -- done
      dsimp only [chan.nonblockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sh.done', γdone
      isplitr
      · ipureintro; rfl
      iframe #
      iapply blocking_rcv_implies_nonblocking
      iapply broadcast_chan_receive _ _ _ _ _ $$ Hdone
      iintro ⟨#Htasks, -⟩
      wp_auto
      wp_for_post
      iapply HΦ
      itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- get a request
      dsimp only [chan.nonblockingClausePre]
      iexists GoString, inferInstance, inferInstance, inferInstance, inferInstance, wv.queue', γqueue
      isplitr
      · ipureintro; rfl
      ihave #Hqch := is_bag_is_chan _ _ _ $$ Hqueue
      iframe Hqch
      iapply blocking_rcv_implies_nonblocking
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hqueue
      inext
      iintro %v Hv
      wp_auto
      wp_apply wp_Worker_process γ w v sh $$ [Hv]
      · iframe #
        iframe
      wp_for_post
      iframe
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- help a worker steal from this one
      dsimp only [chan.nonblockingClausePre]
      iexists GoChan, inferInstance, inferInstance, inferInstance, inferInstance, wv.steal', γsteal
      isplitr
      · ipureintro; rfl
      ihave #Hsch := is_bag_is_chan _ _ _ $$ Hsteal
      iframe Hsch
      iapply blocking_rcv_implies_nonblocking
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hsteal
      inext
      iintro %reply_ch ⟨%γreply, #Hreply_ch⟩
      wp_auto_lc 2
      wp_apply_core chan.wp_select_nonblocking
      isplit
      · iapply BigAndL.bigAndL_singleton.2
        dsimp only [chan.nonblockingClausePre]
        iexists GoString, inferInstance, inferInstance, inferInstance, inferInstance, wv.queue', γqueue
        isplitr
        · ipureintro; rfl
        ihave #Hqch := is_bag_is_chan _ _ _ $$ Hqueue
        iframe Hqch
        iapply blocking_rcv_implies_nonblocking
        iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hqueue
        inext
        iintro %v Hv
        wp_auto
        wp_apply wp_bag_send γreply reply_ch doc_ptr (stealReplyPred γ) $$ [Hv doc]
        · iframe #
          unfold stealReplyPred
          split
          · itrivial
          · iexists v
            iframe
        wp_for_post
        iframe
      · wp_auto
        wp_apply wp_bag_send γreply reply_ch null (stealReplyPred γ) $$ []
        · iframe #
          unfold stealReplyPred
          simp only [↓reduceIte]
          itrivial
        wp_for_post
        iframe
    · iapply BigAndL.bigAndL_nil.2
      itrivial
  · -- default case; try to steal
    wp_auto
    wp_apply chan.wp_make2 (V := Loc) (W64 1) $$ [] as %reply %γreply ⟨#Hreply_is, -, Hown⟩
    · ipureintro; decide
    imod start_bag (stealReplyPred (GF := GF) γ) _ reply γreply (by simp) $$ Hreply_is Hown with #Hreply
    icases Hnpt with ∗Hnpt
    iStructNamed Hnpt
    wp_auto_lc 2
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- done
      dsimp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sh.done', γdone
      isplitr
      · ipureintro; rfl
      iframe #
      iapply broadcast_chan_receive _ _ _ _ _ $$ Hdone
      iintro ⟨#Htasks, -⟩
      wp_auto
      wp_for_post
      iapply HΦ
      itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- request to steal was sent
      dsimp only [chan.blockingClausePre]
      iexists GoChan, inferInstance, inferInstance, inferInstance, inferInstance, nv.steal', γsteal_n,
        reply
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      ihave #Hnsch := is_bag_is_chan _ _ _ $$ Hsteal_n
      iframe Hnsch
      iapply bag_send_au $$ [$Hlc1 $Hlc2] Hsteal_n []
      · iexists γreply
        iframe #
      inext
      wp_auto
      wp_apply wp_bag_receive γreply reply (stealReplyPred γ) $$ Hreply as %v Hv
      wp_if_destruct
      · wp_for_post
        iframe
      · unfold stealReplyPred
        simp only [Hif, ↓reduceIte]
        icases Hv with ⟨%req, Hreq, Htask⟩
        wp_auto
        wp_apply wp_Worker_process γ w req sh $$ [Htask]
        · iframe #
          iframe
        wp_for_post
        iframe
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- received local work while trying to steal
      dsimp only [chan.blockingClausePre]
      iexists GoString, inferInstance, inferInstance, inferInstance, inferInstance, wv.queue', γqueue
      isplitr
      · ipureintro; rfl
      ihave #Hqch := is_bag_is_chan _ _ _ $$ Hqueue
      iframe Hqch
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hqueue
      inext
      iintro %v Hv
      wp_auto
      wp_apply wp_Worker_process γ w v sh $$ [Hv]
      · iframe #
        iframe
      wp_for_post
      iframe
    · iapply BigAndL.bigAndL_nil.2
      itrivial

end proof

end Perennial
