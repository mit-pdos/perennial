From New.proof Require Import proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_spec_inv chan_ghost_state chan_spec_api chan_spec_base.
From New.code.github_com.goose_lang.goose.testdata.examples Require Import channel.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples Require Import channel.

From Perennial.Helpers Require Import bytes.
From Coq Require Import Program.Equality.
Set Default Proof Using "Type*".

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}. 
Context  `{!chanGhostStateG Σ}.
Context `{!ghost_varG Σ (w64)}.
Context `{!goGlobalsGS Σ}.
#[global] Program Instance : IsPkgInit chan_spec_raw_examples := ltac2:(build_pkg_init ()).

Lemma wp_CoordinatedChannelClose (γ: chan_names):
  {{{ is_pkg_init chan_spec_raw_examples }}}
    chan_spec_raw_examples @ "CoordinatedChannelClose" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start; wp_auto.
  wp_apply wp_fupd.

  (* Allocate two ghost variables for distinguishing send cases *)
  iMod (ghost_var_alloc (W64 42)) as (γs1) "HSend42".
  iMod (ghost_var_alloc (W64 84)) as (γs2) "HSend84".

  (* Allocate buffered channel for sending 42 or 84 *)
  wp_apply (wp_NewChannelRef_base w64
    2 (* buffered size *)
    false (* single party *)
    (λ i (v: w64), emp)%I
    (λ (v:w64),
      (ghost_var γs1 1%Qp (W64 42) ∗ ⌜v = W64 42⌝) ∨
      (ghost_var γs2 1%Qp (W64 84) ∗ ⌜v = W64 84⌝)
    )%I
    (λ i, True)%I
    True%I
    (λ n, ⌜n = 2%nat⌝)%I).
  all: try done.
  iIntros (buf_ch mu1 ch_buf_slice1 γ1 buff_params) "Hbuffchan".
  iNamed "Hbuffchan". iDestruct "HCh" as "#HCh".
  iDestruct "Hbuffchan" as "[Hclosedtok Hrest]". iNamed "Hrest".
  iModIntro.
  wp_auto.

  (* Allocate unbuffered sync channel for controlling coordination *)
  wp_apply (wp_NewChannelRef_base w64
    0 (* unbuffered *)
    true (* single party *)
    (λ i _, if decide (i = 0) then own_send_counter_frag (buff_params.(ch_γ w64)) 1 (1/2)%Qp else False)%I
    (λ (v: w64), True)%I
    (λ i, True)%I
    True%I
    (λ n, False)%I).
  all: try done.
  iIntros (sync_ch mu2 ch_buf_slice2 γ2 sync_params) "(%Hsyncparams & #Hsyncchan & Hctsync & HScsync & HRecvPermSync)".
  wp_auto.
  iNamed "HCh".
  iDestruct "Hsyncchan" as "(#musync  & #buffsync & %Hbuffsizesync & %Hbuffltsync & %Hmaxsync & #Hlocksync)".

  (* Ensure channels are valid (non-null) *)
  iDestruct (chan_pointsto_non_null w64 (buff_params.(ch_mu w64)) buff_params with "mu") as %HBufNonNull.
  assert (buff_params.(ch_loc w64) ≠ null) as HBufNotNull by (intro; congruence).
  iDestruct (chan_pointsto_non_null w64 (sync_params.(ch_mu w64)) sync_params with "musync") as %HSyncNonNull.
  assert (sync_params.(ch_loc w64) ≠ null) as HSyncNotNull by (intro; congruence).
  iPersist "syncCh" as "#syncCh".
  iPersist "bufCh" as "#bufCh".
  iDestruct "HSc" as "[HMainBuffSend HForkBuffSend]".
  iDestruct "Hparams" as "%".

  (* Fork worker thread to send 42 and 0 *)
  wp_apply (wp_fork with "[HScsync HForkBuffSend HSend42]").
  {

    replace sync_ch with (sync_params.(ch_loc w64)) by (subst;done).
    replace buf_ch with buff_params.(ch_loc w64) by (subst;done).
    (* Send 42 on buffered channel *)
    wp_apply ((wp_Channel__Send w64 buff_params 0%nat (1/2)%Qp (W64 42)) with "[HForkBuffSend HSend42 bufCh]"). all: try (subst;done).
    { 
      iFrame "#%". unfold P. iFrame. subst. simpl. iSplitL "";first done. 
      iLeft. iFrame. done.
    }
    iIntros "HSendDone".
    wp_auto.

    (* Send 0 on sync channel to join forked sender so we can safely close *)
    wp_apply ((wp_Channel__Send w64 sync_params 0%nat 1%Qp (W64 0)) with "[HScsync syncCh HSendDone]").
    all: try (subst;done).
    { iFrame "#". subst. simpl. unfold send_post. simpl. iDestruct "HSendDone" as "[_ Hsc]".
      iFrame. iPureIntro; done. }
    iIntros "_".
    wp_auto. done.
  }

  replace sync_ch with (sync_params.(ch_loc w64)) by (subst;done).
  replace buf_ch with buff_params.(ch_loc w64) by (subst;done).
  (* Send 84 on buffered channel *)
  wp_apply ((wp_Channel__Send w64 buff_params 0%nat (1/2)%Qp (W64 84)) with "[bufCh HMainBuffSend HSend84]"). all: try (subst;done).
  { iFrame "#". unfold P. subst. simpl. iFrame "%". iFrame. iSplitL "";first done.
    iRight. iFrame. done. 
  }
  iIntros "HSendDone84".
  wp_auto.

  (* Receive discard from sync channel *)
  wp_apply ((wp_Channel__ReceiveDiscardOk w64 sync_params 0%nat 1%Qp (λ n, False)%I) with "[HRecvPermSync]").
  {
    subst. simpl. iFrame "%".
    iFrame. iFrame "#". iPureIntro; done.
  }
  iIntros (v ok) "HRecvSync".
  wp_auto.
  iDestruct "HSendDone84" as "[_ Hscf]".

  destruct ok.
  - (* Proceed to close the buffered channel *)
    unfold recv_post.
    iDestruct "HRecvSync" as "[HMainBufSend HRcp]".
    wp_apply ((wp_Channel__Close w64 buff_params 2) with "[HMainBufSend Hscf Hclosedtok]").
    all: try (subst;done).
    { subst. simpl. iFrame. iFrame "#". iFrame "%". unfold send_post. 
      (* Put the send permissions back together *)
      iCombine "HMainBufSend Hscf" as "Hcperm".
      iFrame. iPureIntro;done.
    }

    (* Receive both values from buffered channel *)
    wp_apply ((wp_Channel__Receive w64 buff_params 0%nat 1%Qp (λ n, ⌜n = 2%nat⌝)%I) with "[HRecvPerm]").
    { subst. simpl. iFrame. iFrame "#". iFrame "%". iPureIntro; done. }
    iIntros (v0 ok0) "HRecv1".
    wp_auto.

    destruct ok0.
    + iDestruct "HRecv1" as "[HP Hrecvperm]". unfold P.
      wp_apply ((wp_Channel__Receive w64 buff_params 1%nat 1%Qp (λ n, ⌜n = 2%nat⌝)%I) with "[Hrecvperm]").
        { 
          subst. simpl. iFrame. iFrame "#". iFrame "%". simpl. iPureIntro; done. 
        }
        iIntros (v1 ok1) "HRecv2".
        wp_auto.

        destruct ok1.
      *

       unfold recv_post.
      iDestruct "HRecv2" as "[HP2 HRecvPerm2]". unfold P. subst. simpl.
      (* Handle possible orderings of buffered results *)
       iDestruct "HP" as "[[Hg42 %H42]|[Hg84 %H84]]". 
       {
        iDestruct "HP2" as "[[Hg42' %H42']|[Hg84' %H84']]".  
        {
          subst v1. simpl. subst v0.   
          iCombine "Hg42 Hg42'" as "Hinvalid" gives "(%Hinvalid & %Hv)".
          done.  
        }
        {
         subst v1. simpl. subst v0. wp_auto. iApply "HΦ". done. 
        }
       }
       {
        iDestruct "HP2" as "[[Hg42' %H42']|[Hg84' %H84']]".  
        {
         subst v1. simpl. subst v0. wp_auto. iApply "HΦ". done. 
        }
        {
          subst v1. simpl. subst v0.   
          iCombine "Hg84 Hg84'" as "Hinvalid" gives "(%Hinvalid & %Hv)".
          done.  
        }
       }
      * wp_auto. iNamed "HRecv2". iNamed "HRecv2". unfold own_recv_perm.
        iNamed "HRcp". iDestruct "HRi" as "%". 
        iDestruct "HRcp" as "[HRcp Hoct]".
        subst n.
        (* We must receive 2 elements which we contracted through Ri, can't be closed here *)
        iDestruct (recv_counter_elem buff_params.(ch_γ w64)  with "[$Hrca] [$HRecFrag]") as "%Hag2".
        done.
    + iNamed "HRecv1". iNamed "HRecv1". iDestruct "HRi" as "%". subst n.
      iDestruct (recv_counter_elem buff_params.(ch_γ w64)  with "[$Hrca] [$HRecFrag]") as "%Hag2".
      done.
  - (* We agreed not to close the sync channel in sync_params R *)
    iNamed "HRecvSync". iNamed "HRecvSync". done. 
Qed.

Definition hello_world_pred
(z: Z) (v: byte_string): iProp Σ :=
 (⌜ v = "hello world"%go ⌝%I) 
.

Lemma wp_SendMessage (γ: chan_names):
  {{{ is_pkg_init chan_spec_raw_examples }}}
    chan_spec_raw_examples @ "SendMessage" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start; wp_auto.

  (* Allocate an unbuffered sync channel with hello_world_pred *)
  wp_apply (wp_NewChannelRef_simple_unbuffered_sync
              byte_string
              hello_world_pred).
  iIntros (msg_ch_ptr mu ch_buf_slice ch_γ_names params) "HChan".
  iNamed "HChan". iNamed "HCh".
  wp_auto.

  (* Validate channel pointer is non-null *)
  iDestruct (chan_pointsto_non_null byte_string (params.(ch_mu byte_string)) params with "mu") as %HMsgNonNull.
  assert (params.(ch_loc byte_string) ≠ null) as HMsgNotNull by (intro; congruence).
  iPersist "messageChan" as "#messageChan".

  (* Fork off sender thread *)
  wp_apply (wp_fork with "[HSc]").
  {
    replace msg_ch_ptr with (params.(ch_loc byte_string)) by (subst;done).
    (* Send "hello world" on the message channel *)
    wp_apply ((wp_Channel__Send byte_string params 0%nat 1%Qp "hello world"%go) with "[messageChan HSc]").
    all: try (subst;done).
    { iFrame "#". iFrame "%". iFrame. unfold P. subst. simpl. iFrame. iPureIntro; done. }
    iIntros "_". wp_auto. done.
  }

  replace msg_ch_ptr with (params.(ch_loc byte_string)) by (subst;done).
  (* Main thread discards the received message *)
  wp_apply ((wp_Channel__ReceiveDiscardOk byte_string params 0%nat) with "[HRecvPerm]").
  {
    iFrame "#".
    unfold Q. subst. simpl. iFrame. iPureIntro; done.
  }
  iIntros (v ok) "HRecvPost".
  wp_auto.

  destruct ok.
  - (* Received successfully *)
    unfold recv_post, hello_world_pred.
    iDestruct "HRecvPost" as "[HP HRecvPerm]".
    unfold P. subst. simpl. iDestruct "HP" as "%HP".
    subst v.
    destruct bool_decide eqn:HDecide.
    + wp_auto. iApply "HΦ". done.
    + done.
  - (* We agreed not to close *)
    iNamed "HRecvPost". iNamed "HRecvPost". done.
Qed.

End proof.