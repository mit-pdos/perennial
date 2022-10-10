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

  set (newepoch:=word.add st.(mp_epoch) 1).
  set (replyInv:=(
                  ∃ (numReplies:u64) (reply_ptrs:list loc),
                    "HnumReplies" ∷ numReplies_ptr ↦[uint64T] #numReplies ∗
                    "Hreplies_sl" ∷ is_slice_small replies_sl ptrT 1 reply_ptrs ∗
                    "#Hreplies" ∷ ([∗ list] i ↦ reply_ptr ; γsrv' ∈ reply_ptrs ; conf,
                    ⌜reply_ptr = null⌝ ∨ (∃ reply σ, enterNewEpochReply.own reply_ptr reply 1 ∗
                                              □(if decide (reply.(enterNewEpochReply.err) = (U64 0)) then
                                                enterNewEpoch_post γsrv reply.(enterNewEpochReply.acceptedEpoch)
                                                                                newepoch σ
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
  iIntros (numReplies_cond) "HnumReplies_cond".
  wp_pures.
  wp_apply (wp_slice_len).
  wp_pures.
Admitted.

End becomeleader_proof.
