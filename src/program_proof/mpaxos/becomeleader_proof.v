From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require mpaxos.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.mpaxos Require Export definitions.

Section becomeleader_proof.

Context `{!heapGS Σ}.
Context {mp_record:MPRecord}.
Notation OpType := (mp_OpType mp_record).
Notation has_op_encoding := (mp_has_op_encoding mp_record).
Notation next_state := (mp_next_state mp_record).
Notation compute_reply := (mp_compute_reply mp_record).
Notation is_Server := (is_Server (mp_record:=mp_record)).
Notation is_singleClerk := (is_singleClerk (mp_record:=mp_record)).

Context (conf:list mp_server_names).
Context `{!mpG Σ}.

Lemma wp_Server__becomeLeader s γ γsrv :
  {{{
        is_Server conf s γ γsrv
  }}}
    mpaxos.Server__becomeLeader #s
  {{{
        RET #(); True
  }}}.
Proof.
  iIntros (Φ) "#Hsrv HΦ".
  wp_call.
  iNamed "Hsrv".
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".

  wp_pures.
  wp_loadField.
  wp_if_destruct.
  { (* already leader, no need to do anything *)
    admit.
  }
  wp_loadField.
  wp_pures.
  wp_loadField.
  wp_apply (wp_allocStruct).
  { repeat econstructor. }
  iIntros (args_ptr) "Hargs".
  wp_pures.
  wp_loadField.
  wp_apply (release_spec with "[-HΦ Hargs]").
  {
    iFrame "HmuInv Hlocked".
    iNext.
    iExists _,_,_,_,_,_.
    iFrame "∗#%".
  }

  wp_pures.
  wp_apply (wp_ref_to).
  { eauto. }
  iIntros (numReplies_ptr) "HnumReplies".
  wp_pures.

  iMod (readonly_load with "Hclerks_sl") as (?) "Hclerks_sl2".
  iDestruct (is_slice_small_sz with "Hclerks_sl2") as "%Hclerks_sz".
  iClear "Hclerks_sl2".
  clear q.

  wp_apply (wp_slice_len).
  wp_apply (wp_NewSlice).
  iIntros (replies_sl) "Hreplies_sl".
  wp_pures.
  rewrite -Hclerks_sz.

  set (newepoch:=word.add st.(mp_epoch) 1%Z).
  set (replyInv:=(
                  ∃ (numReplies:u64) (reply_ptrs:list loc),
                    "HnumReplies" ∷ numReplies_ptr ↦[uint64T] #numReplies ∗
                    "Hreplies_sl" ∷ is_slice_small replies_sl ptrT 1 reply_ptrs ∗
                    "Hreplies" ∷ ([∗ list] i ↦ reply_ptr ; γsrv' ∈ reply_ptrs ; conf,
                    ⌜reply_ptr = null⌝ ∨ (∃ reply, enterNewEpochReply.own reply_ptr reply 1 ∗
                                              □(if decide (reply.(enterNewEpochReply.err) = (U64 0)) then
                                                enterNewEpoch_post γsrv' reply newepoch
                                              else
                                                True)
                                  ))
                )%I).
  wp_apply (newlock_spec mpN _ replyInv with "[HnumReplies Hreplies_sl]").
  {
    iNext.
    iExists _, _.
    iDestruct (is_slice_to_small with "Hreplies_sl") as "$".
    iFrame "∗".
    iDestruct (big_sepL2_length with "Hclerks_rpc") as "%Hlen".
    iApply big_sepL2_impl.
    {
      instantiate (1:=(λ _ _ _, True)%I).
      simpl.
      iApply big_sepL2_forall.
      iIntros.
      iSplit.
      {
        iPureIntro.
        rewrite Hlen.
        by rewrite replicate_length.
      }
      done.
    }
    iModIntro.
    iIntros.
    iLeft.
    rewrite lookup_replicate in H.
    naive_solver.
  }
  iIntros (muReply) "#HmuReplyInv".
  wp_pures.
  wp_apply (wp_newCond with "HmuReplyInv").
  iIntros (numReplies_cond) "#HnumReplies_cond".
  wp_pures.
  wp_apply (wp_slice_len).
  wp_pures.

  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  iMod (readonly_alloc_1 with "epoch") as "#Hargs_epoch".

  iMod (readonly_load with "Hclerks_sl") as (?) "Hclerks_sl2".
  wp_apply (wp_forSlice (λ _, True%I) (V:=loc) with "[] [$Hclerks_sl2]").
  { (* loop iteration *)
    clear Φ.
    iIntros (?? Φ) "!# (_ & %Hi_le & %Hi_lookup) HΦ".
    wp_call.
    wp_apply (wp_fork with "[]").
    { (* make applyAsFollower RPC and put reply in the replies list *)
      iNext.
      wp_apply (wp_allocStruct).
      { Transparent slice.T. repeat econstructor. Opaque slice.T. }
      iIntros (reply_ptr) "Hreply".
      wp_pures.

      (* establish is_singleClerk *)
      iDestruct (big_sepL2_lookup_1_some with "Hclerks_rpc") as (?) "%Hi_conf_lookup".
      { done. }
      iAssert (_) with "Hclerks_rpc" as "Hclerks_rpc2".
      iDestruct (big_sepL2_lookup_acc with "Hclerks_rpc2") as "[#His_ck _]".
      { done. }
      { done. }
      iMod (readonly_load with "Hargs_epoch") as (?) "Hargs_epoch2".
      wp_apply (wp_singleClerk__enterNewEpoch with "[$His_ck Hreply Hargs_epoch2]").
      {
        iFrame.
        instantiate (3:=enterNewEpochArgs.mkC newepoch).
        iFrame.
        iDestruct (struct_fields_split with "Hreply") as "HH".
        iNamed "HH".
        instantiate (1:=enterNewEpochReply.mkC _ _ _ _).
        iExists _.
        iFrame.
        simpl.
        instantiate (2:=Slice.nil).
        iFrame.
        instantiate (1:=[]).
        iApply (is_slice_small_nil).
        done.
      }
      iIntros (reply) "Hreply".
      wp_pures.

      wp_apply (acquire_spec with "HmuReplyInv").
      iIntros "[Hlocked Hown]".
      iNamed "Hown".
      wp_pures.
      wp_load.
      wp_store.
      iDestruct (big_sepL2_lookup_2_some with "Hreplies") as (?) "%Hi_replies_lookup".
      { done. }
      wp_apply (wp_SliceSet with "[$Hreplies_sl]").
      {
        done.
      }
      iIntros "Hreplies_sl".
      wp_pures.
      wp_load.
      iDestruct "Hreply" as "[Hreply #Hpost]".
      wp_apply (wp_If_optional _ _ (True%I)).
      {
        iIntros (?) "_ HΦ'".
        wp_apply (wp_condSignal with "HnumReplies_cond").
        wp_pures.
        by iApply "HΦ'".
      }
      wp_apply (release_spec with "[-]").
      {
        iFrame "# Hlocked".
        iNext.
        iExists _, _.
        iFrame "∗".
        iApply to_named.
        iDestruct (big_sepL2_insert_acc with "Hreplies")  as "[_ Hreplies]".
        { done. }
        { done. }
        iDestruct ("Hreplies" $! reply_ptr x2 with "[Hreply]") as "Hreplies".
        {
          iRight.
          iExists _.
          iFrame.
          iModIntro.
          destruct (decide (_)).
          {
            simpl.
            iFrame "Hpost".
          }
          done.
        }

        replace (<[int.nat i:=x2]> conf) with (conf) ; last first.
        {
          symmetry.
          by apply list_insert_id.
        }
        iFrame "Hreplies".
      }
      done.
    }
    iApply "HΦ".
    done.
  }
  (* done with loop *)
  iIntros "_".
  wp_pures.

  wp_apply (acquire_spec with "HmuReplyInv").
  iIntros "[Hlocked Hown]".
  wp_pures.

  wp_forBreak_cond.
  wp_pures.
  iNamed "Hown".
  wp_load.
  wp_if_destruct.
  { (* continue waiting for there to be enough replies *)
    wp_pures.
    wp_apply (wp_condWait with "[$HnumReplies_cond $HmuReplyInv $Hlocked Hreplies_sl Hreplies HnumReplies]").
    {
      iExists _, _.
      iFrame "∗#".
    }
    iIntros "[Hlocked Hown]".
    wp_pures.
    iLeft.
    iFrame.
    iModIntro.
    done.
  }
  (* done waiting, have enough replies now *)
  iModIntro.
  iRight.
  iSplitR; first done.

  wp_pures.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (latestReply_ptr) "HlatestReply".
  wp_pures.

  wp_apply (wp_ref_to).
  { eauto. }
  iIntros (numSuccesses_ptr) "HnumSuccesses".
  wp_pures.
Admitted.

End becomeleader_proof.
