From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require paxos.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial Require Export paxos.definitions paxos.enternewepoch_proof.

Section becomeleader_proof.

Context `{!heapGS Σ}.

Context `{!paxosG Σ}.
Context `{Hparams:!paxosParams.t Σ}.
Import paxosParams.

Lemma wp_Server__TryBecomeLeader s γ γsrv Ψ Φ :
  is_Server s γ γsrv -∗
  (Ψ -∗ Φ #()) -∗
  becomeLeader_core_spec Ψ -∗
  WP Server__TryBecomeLeader #s {{ Φ }}
.
Proof.
  iIntros "#Hsrv HΦ HΨ".
  wp_call.
  iNamed "Hsrv".
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".

  wp_pures.
  iNamed "Hvol".
  wp_loadField.
  wp_loadField.
  wp_if_destruct.
  { (* already leader, no need to do anything *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ HΨ]").
    {
      do 2 iFrame "∗#%". by rewrite Heqb.
    }
    wp_pures.
    iModIntro.
    by iApply "HΦ".
  }
  wp_loadField.
  wp_pures.
  wp_loadField. wp_loadField.
  wp_apply (wp_allocStruct).
  { repeat econstructor. }
  iIntros (args_ptr) "Hargs".
  wp_pures.
  wp_loadField.
  wp_apply (release_spec with "[-HΦ Hargs HΨ]").
  {
    do 2 iFrame "∗#%". by rewrite Heqb.
  }

  wp_pures.
  wp_apply (wp_ref_to).
  { eauto. }
  iIntros (numReplies_ptr) "HnumReplies".
  wp_pures.

  iMod (readonly_load with "Hclerks_sl") as (?) "Hclerks_sl2".
  iDestruct (own_slice_small_sz with "Hclerks_sl2") as "%Hclerks_sz".
  iClear "Hclerks_sl2".
  clear q.

  wp_apply (wp_slice_len).
  wp_apply (wp_NewSlice).
  iIntros (replies_sl) "Hreplies_sl".
  wp_pures.
  rewrite -Hclerks_sz.

  set (newepoch:=word.add pst.(paxosState.epoch) 1%Z).
  iMod (ghost_var_alloc ()) as (γescrow) "HreplyPostEscrow".
  set (replyInv:=(
                  ∃ (numReplies:u64) (reply_ptrs:list loc),
                    "%HlenEq" ∷ ⌜length reply_ptrs = length γ.(s_hosts) ⌝ ∗
                    "HnumReplies" ∷ numReplies_ptr ↦[uint64T] #numReplies ∗
                    "Hreplies_sl" ∷ own_slice_small replies_sl ptrT (DfracOwn 1) reply_ptrs ∗
                    "Hreplies" ∷ (ghost_var γescrow 1 () ∨ [∗ list] i ↦ reply_ptr ; γsrv' ∈ reply_ptrs ; γ.(s_hosts),
                    ⌜reply_ptr = null⌝ ∨ (∃ reply, (enterNewEpochReply.own reply_ptr reply (DfracOwn 1)) ∗
                                              (if decide (reply.(enterNewEpochReply.err) = (W64 0)) then
                                                enterNewEpoch_post γ γsrv' reply newepoch
                                              else
                                                True)
                                  ))
                )%I).
  wp_apply (newlock_spec N _ replyInv with "[HnumReplies Hreplies_sl]").
  {
    iNext.
    iExists _, _.
    iDestruct (own_slice_to_small with "Hreplies_sl") as "$".
    iFrame "∗".
    iDestruct (big_sepL2_length with "Hclerks_rpc") as "%Hlen".
    iSplitR.
    {
      iPureIntro.
      rewrite replicate_length.
      word.
    }
    iRight.
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

      (* establish is_singleClerk *)
      iDestruct (big_sepL2_lookup_1_some with "Hclerks_rpc") as (?) "%Hi_conf_lookup".
      { done. }
      iAssert (_) with "Hclerks_rpc" as "Hclerks_rpc2".
      iDestruct (big_sepL2_lookup_acc with "Hclerks_rpc2") as "[#His_ck _]".
      { done. }
      { done. }
      iMod (readonly_load with "Hargs_epoch") as (?) "Hargs_epoch2".
      wp_apply (wp_singleClerk__enterNewEpoch with "[$His_ck Hargs_epoch2]").
      {
        iFrame.
        instantiate (2:=enterNewEpochArgs.mkC newepoch).
        iFrame.
      }
      iIntros (reply_ptr reply) "Hreply".
      wp_pures.

      wp_apply (acquire_spec with "HmuReplyInv").
      iIntros "[Hlocked Hown]".
      iNamed "Hown".
      wp_pures.
      wp_load.
      wp_store.
      pose proof (lookup_lt_Some _ _ _ Hi_conf_lookup) as Hineq.
      rewrite -HlenEq in Hineq.
      apply (list_lookup_lt) in Hineq.
      destruct Hineq as [? Hi_replies_lookup].

      wp_apply (wp_SliceSet with "[$Hreplies_sl]").
      {
        done.
      }
      iIntros "Hreplies_sl".
      wp_pures.
      wp_load.
      iDestruct "Hreply" as "[Hreply Hpost]".
      wp_apply (wp_If_optional _ _ (True%I)).
      {
        iIntros (?) "_ HΦ'".
        wp_apply (wp_condSignal with "HnumReplies_cond").
        wp_pures.
        by iApply "HΦ'".
      }
      (* iMod (readonly_alloc_1 with "Hreply") as "Hreply". *)
      wp_apply (release_spec with "[-]").
      {
        iFrame "# Hlocked".
        iNext.
        iExists _, _.
        iFrame "∗".
        iSplitR.
        {
          iPureIntro.
          rewrite insert_length.
          word.
        }
        iDestruct "Hreplies" as "[$|Hreplies]".
        iApply to_named.
        iRight.
        iDestruct (big_sepL2_insert_acc with "Hreplies")  as "[_ Hreplies2]".
        { done. }
        { done. }
        iDestruct ("Hreplies2" $! reply_ptr x2 with "[Hreply Hpost]") as "Hreplies3".
        {
          iRight.
          iExists _.
          iFrame.
        }

        replace (<[uint.nat i:=x2]> γ.(s_hosts)) with (γ.(s_hosts)) ; last first.
        {
          symmetry.
          by apply list_insert_id.
        }
        iFrame "Hreplies3".
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
      iFrame "∗#%".
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

  iDestruct "Hreplies" as "[Hbad|Hreplies]".
  {
    iDestruct (ghost_var_valid_2 with "Hbad HreplyPostEscrow") as %Hbad.
    exfalso.
    naive_solver.
  }

  set (I:=λ (i:u64), (
                 ∃ (W: gset nat) (latestReply_loc:loc),
                 "%HW_in_range" ∷ ⌜∀ s, s ∈ W → s < uint.nat i⌝ ∗
                 "%HW_size_nooverflow" ∷ ⌜(size W) ≤ uint.nat i⌝ ∗
                 "HnumSuccesses" ∷ numSuccesses_ptr ↦[uint64T] #(W64 (size W)) ∗
                 "HlatestReply_loc" ∷ latestReply_ptr ↦[ptrT] #latestReply_loc ∗
                 "Hreplies" ∷ ([∗ list] j ↦ reply_ptr ; γsrv' ∈ reply_ptrs ; γ.(s_hosts) ,
                  ⌜uint.nat i ≤ j⌝ →
                 ⌜reply_ptr = null⌝ ∨ (∃ reply, (enterNewEpochReply.own reply_ptr reply (DfracOwn 1)) ∗
                                           (if decide (reply.(enterNewEpochReply.err) = (W64 0)) then
                                             enterNewEpoch_post γ γsrv' reply newepoch
                                           else
                                             True)
                               )) ∗
                 if (decide (size W = 0)) then
                   True
                 else
                   ∃ latestReply latestLog,
                  "HlatestReply" ∷ (enterNewEpochReply.own latestReply_loc latestReply (DfracOwn 1)) ∗
                  "%Hlatestlog" ∷ ⌜latestReply.(enterNewEpochReply.state) = get_state latestLog⌝ ∗
                  "%HlatestlogLen" ∷ ⌜uint.nat latestReply.(enterNewEpochReply.nextIndex) = length latestLog⌝ ∗
                  "%HlatestEpoch_ineq" ∷ ⌜uint.nat latestReply.(enterNewEpochReply.acceptedEpoch) < uint.nat newepoch⌝ ∗
                  "#Hlatest_prop" ∷ is_proposal (config:=γ.(s_hosts)) (N:=N)
                                  γ.(s_mp) latestReply.(enterNewEpochReply.acceptedEpoch) latestLog ∗
                  "#HP_latest" ∷ (□ Pwf latestReply.(enterNewEpochReply.state)) ∗
                  "#Hacc_lbs" ∷ (□ [∗ list] s ↦ γsrv' ∈ γ.(s_hosts), ⌜s ∈ W⌝ →
                                        is_accepted_upper_bound γsrv' latestLog
                                                                latestReply.(enterNewEpochReply.acceptedEpoch)
                                                                newepoch
                                ) ∗
                  "Hvotes" ∷ ([∗ list] s ↦ γsrv' ∈ γ.(s_hosts), ⌜s ∈ W⌝ → own_vote_tok γsrv' newepoch)
      )%I).

  wp_apply (wp_forSlice (V:=loc) I _ _ _ _ _ reply_ptrs with "[] [HnumSuccesses HlatestReply Hreplies_sl Hreplies]").
  2: {
    iFrame "Hreplies_sl".
    iExists ∅, null.
    rewrite size_empty.
    simpl.
    iFrame.
    iSplitR; first done.
    iSplitR; first done.
    iDestruct (big_sepL2_impl with "Hreplies []") as "$".
    iModIntro.
    iIntros.
    done.
  }
  { (* one iteration of loop *)
    clear Φ.
    iIntros (?? Φ) "!# (Hi & %Hi_lt & %Hi_lookup) HΦ".
    iNamed "Hi".
    wp_pures.
    wp_if_destruct.
    {
      iDestruct (big_sepL2_lookup_1_some with "Hreplies") as (?) "%Hi_conf_lookup".
      { done. }
      iDestruct (big_sepL2_lookup_acc_impl with "Hreplies") as "[Hreply_post Hreplies]".
      { done. }
      { done. }
      iSpecialize ("Hreply_post" with "[% //]").
      iDestruct "Hreply_post" as "[%Hbad|Hreply_post]".
      {
        exfalso. rewrite Hbad in Heqb1. done.
      }
      iDestruct "Hreply_post" as (?) "[Hreply Hpost]".
      iNamed "Hreply".
      wp_loadField.
      wp_if_destruct.
      { (* got ENone, increase size of W *)
        wp_load.
        wp_if_destruct.
        { (* this is the first successful reply, no need to compare with other replies *)
          wp_store.
          wp_pures.
          wp_load.
          wp_store.
          replace (W) with (∅:gset nat); last first.
          {
            assert (size W = 0) as Hsz.
            {
              apply (f_equal uint.Z) in Heqb3.
              rewrite Z_u64 in Heqb3.
              2:{ word. }
              replace (uint.Z (W64 0)) with (0%Z) in Heqb3 by word.
              word.
            }
            apply size_empty_inv in Hsz.
            by apply leibniz_equiv.
          }
          iModIntro.
          iApply "HΦ".

          iExists {[ uint.nat i ]}, x.
          iSplitR.
          {
            iPureIntro.
            intros ? Hin.
            apply elem_of_singleton_1 in Hin as ->.
            word.
          }
          iSplitR.
          {
            iPureIntro.
            rewrite size_singleton.
            word.
          }
          iFrame.
          rewrite size_singleton.
          rewrite size_empty.
          iFrame.
          simpl.
          destruct (decide (_)); last first.
          { exfalso. done. }
          iDestruct "Hpost" as (?) "(%Hepoch_ineq & %Hlog & %Hlen & #Hacc_ub & #Hprop & #HP2 & Hvote)".
          iSplitL "Hreplies".
          {
            iApply "Hreplies".
            {
              iModIntro.
              iIntros (??????) "Hwand".
              iIntros (?).
              iApply "Hwand".
              iPureIntro.
              replace (uint.nat (word.add i 1%Z)) with (uint.nat i + 1) in * by word.
              word.
            }
            {
              iIntros.
              exfalso.
              replace (uint.nat (word.add i 1%Z)) with (uint.nat i + 1) in * by word.
              word.
            }
          }
          iExists log.
          iSplitR; first done.
          iFrame "#%".
          iSplitR "Hvote"; last first.
          {
            iDestruct (big_sepL_lookup_acc_impl with "[]") as "[_ Hwand]".
            { exact Hi_conf_lookup. }
            { by iApply big_sepL_emp. }
            iApply ("Hwand" with "[] [Hvote]").
            {
              iModIntro.
              iIntros.
              exfalso.
              rewrite elem_of_singleton in H2.
              done.
            }
            {
              iIntros.
              iFrame "Hvote".
            }
          }
          iModIntro.
          iApply big_sepL_forall.
          iIntros.
          replace (x0) with (x2); last first.
          {
            apply elem_of_singleton_1 in H0.
            rewrite H0 in H.
            rewrite H in Hi_conf_lookup.
            by injection Hi_conf_lookup.
          }
          iFrame "#".
        }
        { (* In this case, there have been previous successful replies. Compare with latestReply *)
          wp_load.
          destruct (decide (size W = 0)).
          { exfalso.
            apply Heqb3. f_equal. rewrite e.
            done. }
          iNamed "Hi".
          iRename "Hreply_acceptedEpoch" into "Hreply_acceptedEpoch2".
          iRename "Hreply_nextIndex" into "Hreply_nextIndex2".
          iDestruct "Hreply_err" as "?".
          iDestruct "Hreply_ret" as "?".
          iDestruct "Hreply_ret_sl" as "?".
          iNamed "HlatestReply".
          wp_loadField.
          wp_loadField.
          wp_if_destruct.
          { (* case: newreply.acceptedEpoch > latestReply.acceptedEpoch *)
            wp_store.
            wp_pures.
            wp_load.
            wp_store.
            iModIntro.
            iApply "HΦ".

            iExists (W ∪ {[ uint.nat i ]}), x.

            iSplitR.
            {
              iPureIntro.
              intros.
              apply elem_of_union in H as [H|H].
              {
                specialize (HW_in_range s0 H).
                word.
              }
              {
                rewrite elem_of_singleton in H.
                word.
              }
            }
            rewrite size_union; last first.
            {
              apply disjoint_singleton_r.
              destruct (decide (uint.nat i ∈ W)).
              {
                exfalso.
                specialize (HW_in_range (uint.nat i) e).
                word.
              }
              done.
            }
            rewrite size_singleton.
            iSplitR.
            {
              iPureIntro.
              word.
            }
            replace (word.add (size W) 1) with (W64 (size W + 1)%nat) by word.
            iFrame.

            iSplitL "Hreplies".
            { (* XXX: copy/pasted *)
              iApply "Hreplies".
              {
                iModIntro.
                iIntros (??????) "Hwand".
                iIntros (?).
                iApply "Hwand".
                iPureIntro.
                replace (uint.nat (word.add i 1%Z)) with (uint.nat i + 1) in H2 by word.
                word.
              }
              {
                iIntros.
                exfalso.
                replace (uint.nat (word.add i 1%Z)) with (uint.nat i + 1) in H by word.
                word.
              }
            }

            destruct (decide (size W + 1 = 0)).
            { done. }

            destruct (decide (_)); last first.
            { exfalso. done. }
            iDestruct "Hpost" as (?) "(%Hepoch_ineq & %Hlog & %Hlen & #Hacc_ub & #Hprop & #HP2 & Hvote)".
            iExists reply, log.
            iSplitR "Hvote Hvotes Hprop".
            {
              repeat iExists _; iFrame "∗#".
            }
            iFrame "Hprop %".
            iFrame "#".
            iSplitR "Hvotes Hvote"; last first.
            { (* accumulate votes *)
              iDestruct (big_sepL_lookup_acc_impl with "Hvotes") as "[_ Hwand]".
              { exact Hi_conf_lookup. }
              iApply ("Hwand" with "[] [Hvote]").
              {
                iModIntro.
                iIntros (????) "Hwand".
                iIntros "%Hk".
                rewrite elem_of_union in Hk.
                destruct Hk as [Hk|Hbad].
                {
                  iApply "Hwand".
                  done.
                }
                {
                  exfalso.
                  rewrite elem_of_singleton in Hbad.
                  done.
                }
              }
              {
                iIntros.
                iFrame "Hvote".
              }
            }

            iModIntro.
            iApply (big_sepL_impl with "Hacc_lbs").
            iModIntro.
            iIntros (???) "#Hwand".
            iIntros "%Hin".

            rewrite elem_of_union in Hin.
            destruct Hin as [Hold|Hnew].
            {
              iSpecialize ("Hwand" with "[%//]").
              iFrame.
              iDestruct (is_accepted_upper_bound_mono_epoch with "Hwand") as "Hwand2".
              { instantiate (1:=reply.(enterNewEpochReply.acceptedEpoch)). word. }
              { done. }
              iDestruct (is_accepted_upper_bound_mono_log with "Hwand2") as "$".
              { apply prefix_nil. }
            }
            {
              rewrite elem_of_singleton in Hnew.
              rewrite Hnew.
              replace (x2) with (x0).
              { iFrame "Hacc_ub". }
              rewrite Hnew in H.
              rewrite H in Hi_conf_lookup.
              by injection Hi_conf_lookup.
            }
          }
          { (* *)
            wp_load.
            wp_loadField.
            wp_loadField.
            wp_pures.
            destruct (bool_decide _) as [] eqn:X.
            { (* case: same epoch *)
              wp_pures.
              wp_load.
              wp_loadField.
              wp_loadField.
              wp_if_destruct.
              { (* reply has higher nextIndex than latestReply *)
                wp_store.
                wp_load.
                wp_store.
                iModIntro.
                iApply "HΦ".

                (* establish loop invariant *)
                iExists (W ∪ {[ uint.nat i ]}), x.
                iSplitR.
                {
                  iPureIntro.
                  intros.
                  apply elem_of_union in H as [H|H].
                  {
                    specialize (HW_in_range s0 H).
                    word.
                  }
                  {
                    rewrite elem_of_singleton in H.
                    word.
                  }
                }
                rewrite size_union; last first.
                {
                  apply disjoint_singleton_r.
                  destruct (decide (uint.nat i ∈ W)).
                  {
                    exfalso.
                    specialize (HW_in_range (uint.nat i) e).
                    word.
                  }
                  done.
                }
                rewrite size_singleton.
                iSplitR.
                {
                  iPureIntro.
                  word.
                }
                replace (word.add (size W) 1) with (W64 (size W + 1)%nat) by word.
                iFrame.

                iSplitL "Hreplies".
                { (* XXX: copy/pasted *)
                  iApply "Hreplies".
                  {
                    iModIntro.
                    iIntros (??????) "Hwand".
                    iIntros (?).
                    iApply "Hwand".
                    iPureIntro.
                    replace (uint.nat (word.add i 1%Z)) with (uint.nat i + 1) in H2 by word.
                    word.
                  }
                  {
                    iIntros.
                    exfalso.
                    replace (uint.nat (word.add i 1%Z)) with (uint.nat i + 1) in H by word.
                    word.
                  }
                }

                destruct (decide (size W + 1 = 0)).
                { done. }

                destruct (decide (_)); last first.
                { exfalso. done. }
                iDestruct "Hpost" as (?) "(%Hepoch_ineq & %Hlog & %Hlen & #Hacc_ub & #Hprop & #HP2 & Hvote)".
                iExists reply, log.
                rewrite sep_exist_r. iExists _; iFrame "∗#%".
                (* XXX: copy/paste votes *)
                iSplitR "Hvotes Hvote"; last first.
                { (* accumulate votes *)
                  iDestruct (big_sepL_lookup_acc_impl with "Hvotes") as "[_ Hwand]".
                  { exact Hi_conf_lookup. }
                  iApply ("Hwand" with "[] [Hvote]").
                  {
                    iModIntro.
                    iIntros (????) "Hwand".
                    iIntros "%Hk".
                    rewrite elem_of_union in Hk.
                    destruct Hk as [Hk|Hbad].
                    {
                      iApply "Hwand".
                      done.
                    }
                    {
                      exfalso.
                      rewrite elem_of_singleton in Hbad.
                      done.
                    }
                  }
                  {
                    iIntros.
                    iFrame "Hvote".
                  }
                }

                iModIntro.
                iApply (big_sepL_impl with "Hacc_lbs").
                iModIntro.
                iIntros (???) "#Hwand".
                iIntros "%Hin".

                rewrite elem_of_union in Hin.
                destruct Hin as [Hold|Hnew].
                {
                  iSpecialize ("Hwand" with "[%//]").
                  iFrame.
                  rewrite X.
                  iDestruct (is_proposal_compare with "Hprop Hlatest_prop") as "%Hpre".
                  {
                    word.
                  }
                  iDestruct (is_accepted_upper_bound_mono_log with "Hwand") as "$".
                  { done. }
                }
                {
                  rewrite elem_of_singleton in Hnew.
                  rewrite Hnew.
                  replace (x2) with (x0).
                  { iFrame "Hacc_ub". }
                  rewrite Hnew in H.
                  rewrite H in Hi_conf_lookup.
                  by injection Hi_conf_lookup.
                }
              }
              { (* keep the old latestReply *)
                wp_pures.
                wp_load.
                wp_store.
                iModIntro.
                iApply "HΦ".

                (* establish loop invariant *)
                iExists (W ∪ {[ uint.nat i ]}), _.
                iSplitR.
                {
                  iPureIntro.
                  intros.
                  apply elem_of_union in H as [H|H].
                  {
                    specialize (HW_in_range s0 H).
                    word.
                  }
                  {
                    rewrite elem_of_singleton in H.
                    word.
                  }
                }
                rewrite size_union; last first.
                {
                  apply disjoint_singleton_r.
                  destruct (decide (uint.nat i ∈ W)).
                  {
                    exfalso.
                    specialize (HW_in_range (uint.nat i) e).
                    word.
                  }
                  done.
                }
                rewrite size_singleton.
                iSplitR.
                {
                  iPureIntro.
                  word.
                }
                replace (word.add (size W) 1) with (W64 (size W + 1)%nat) by word.
                iFrame.

                iSplitL "Hreplies".
                { (* XXX: copy/pasted *)
                  iApply "Hreplies".
                  {
                    iModIntro.
                    iIntros (??????) "Hwand".
                    iIntros (?).
                    iApply "Hwand".
                    iPureIntro.
                    replace (uint.nat (word.add i 1%Z)) with (uint.nat i + 1) in H2 by word.
                    word.
                  }
                  {
                    iIntros.
                    exfalso.
                    replace (uint.nat (word.add i 1%Z)) with (uint.nat i + 1) in H by word.
                    word.
                  }
                }

                destruct (decide (size W + 1 = 0)).
                { done. }
                repeat iExists _.
                rewrite sep_exist_r. repeat iExists _.
                instantiate (1:=enterNewEpochReply.mkC _ _ _ _). simpl.
                iFrame "Hreply_ret ∗".

                destruct (decide (_)); last first.
                { exfalso. done. }
                iDestruct "Hpost" as (?) "(%Hepoch_ineq & %Hlog & %Hlen & #Hacc_ub & #Hprop & #HP2 & Hvote)".

                iFrame "#%".
                (* XXX: copy/paste votes *)
                iSplitR "Hvotes Hvote"; last first.
                { (* accumulate votes *)
                  iDestruct (big_sepL_lookup_acc_impl with "Hvotes") as "[_ Hwand]".
                  { exact Hi_conf_lookup. }
                  iApply ("Hwand" with "[] [Hvote]").
                  {
                    iModIntro.
                    iIntros (????) "Hwand".
                    iIntros "%Hk".
                    rewrite elem_of_union in Hk.
                    destruct Hk as [Hk|Hbad].
                    {
                      iApply "Hwand".
                      done.
                    }
                    {
                      exfalso.
                      rewrite elem_of_singleton in Hbad.
                      done.
                    }
                  }
                  {
                    iIntros.
                    iFrame "Hvote".
                  }
                }

                iModIntro.
                iApply (big_sepL_impl with "Hacc_lbs").
                iModIntro.
                iIntros (???) "#Hwand".
                iIntros "%Hin".

                rewrite elem_of_union in Hin.
                destruct Hin as [Hold|Hnew].
                {
                  iSpecialize ("Hwand" with "[%//]").
                  iFrame.
                  done.
                }
                {
                  rewrite elem_of_singleton in Hnew.
                  rewrite Hnew.
                  rewrite X.

                  iDestruct (is_proposal_compare with "Hlatest_prop Hprop") as %Hpre.
                  {
                    word.
                  }
                  replace (x0) with (x2).
                  {
                    iDestruct (is_accepted_upper_bound_mono_log with "Hacc_ub") as "$".
                    done.
                  }
                  rewrite Hnew in H.
                  rewrite H in Hi_conf_lookup.
                  by injection Hi_conf_lookup.
                }
              }
            }
            (* case: epoch is not the same, so keep the old latest reply *)
            wp_pures.
            wp_load.
            wp_store.
            iModIntro.
            iApply "HΦ".

            (* establish loop invariant *)
            iExists (W ∪ {[ uint.nat i ]}), _.
            iSplitR.
            {
              iPureIntro.
              intros.
              apply elem_of_union in H as [H|H].
              {
                specialize (HW_in_range s0 H).
                word.
              }
              {
                rewrite elem_of_singleton in H.
                word.
              }
            }
            rewrite size_union; last first.
            {
              apply disjoint_singleton_r.
              destruct (decide (uint.nat i ∈ W)).
              {
                exfalso.
                specialize (HW_in_range (uint.nat i) e).
                word.
              }
              done.
            }
            rewrite size_singleton.
            iSplitR.
            {
              iPureIntro.
              word.
            }
            replace (word.add (size W) 1) with (W64 (size W + 1)%nat) by word.
            iFrame.

            (* XXX: copy/pasted *)
            iSplitL "Hreplies".
            {
              iApply "Hreplies".
              {
                iModIntro.
                iIntros (??????) "Hwand".
                iIntros (?).
                iApply "Hwand".
                iPureIntro.
                replace (uint.nat (word.add i 1%Z)) with (uint.nat i + 1) in H2 by word.
                word.
              }
              {
                iIntros.
                exfalso.
                replace (uint.nat (word.add i 1%Z)) with (uint.nat i + 1) in H by word.
                word.
              }
            }

            destruct (decide (size W + 1 = 0)).
            { done. }
            iExists _, _; iFrame "#%".

            destruct (decide (_)); last first.
            { exfalso. done. }
            iDestruct "Hpost" as (?) "(%Hepoch_ineq & %Hlog & %Hlen & #Hacc_ub & #Hprop & #HP2 & Hvote)".
            rewrite sep_exist_r. iExists _; iFrame.
            (* XXX: copy/paste votes *)
            iSplitR "Hvotes Hvote"; last first.
            { (* accumulate votes *)
              iDestruct (big_sepL_lookup_acc_impl with "Hvotes") as "[_ Hwand]".
              { exact Hi_conf_lookup. }
              iApply ("Hwand" with "[] [Hvote]").
              {
                iModIntro.
                iIntros (????) "Hwand".
                iIntros "%Hk".
                rewrite elem_of_union in Hk.
                destruct Hk as [Hk|Hbad].
                {
                  iApply "Hwand".
                  done.
                }
                {
                  exfalso.
                  rewrite elem_of_singleton in Hbad.
                  done.
                }
              }
              {
                iIntros.
                iFrame "Hvote".
              }
            }

            iModIntro.
            iApply (big_sepL_impl with "Hacc_lbs").
            iModIntro.
            iIntros (???) "#Hwand".
            iIntros "%Hin".

            rewrite elem_of_union in Hin.
            destruct Hin as [Hold|Hnew].
            {
              iSpecialize ("Hwand" with "[%//]").
              iFrame.
              done.
            }
            {
              rewrite elem_of_singleton in Hnew.
              rewrite Hnew.

              replace (x0) with (x2).
              {
                rewrite bool_decide_eq_false in X.
                iDestruct (is_accepted_upper_bound_mono_epoch with "Hacc_ub") as "Hacc_ub2".
                {
                  instantiate (1:=latestReply.(enterNewEpochReply.acceptedEpoch)).
                  destruct (decide (uint.nat reply.(enterNewEpochReply.acceptedEpoch) = uint.nat latestReply.(enterNewEpochReply.acceptedEpoch))).
                  {
                    exfalso.
                    replace (reply.(enterNewEpochReply.acceptedEpoch)) with (latestReply.(enterNewEpochReply.acceptedEpoch)) in X by word.
                    done.
                  }
                  word.
                }
                { done. }
                iDestruct (is_accepted_upper_bound_mono_log with "Hacc_ub2") as "$".
                { apply prefix_nil. }
              }
              rewrite Hnew in H.
              rewrite H in Hi_conf_lookup.
              by injection Hi_conf_lookup.
            }
          }
        }
      }
      { (* got error, don't change anything *)
        iModIntro.
        iApply "HΦ".
        iExists W, _.
        iFrame "∗#%".
        replace (uint.nat (word.add i 1%Z)) with (uint.nat i + 1) by word.
        iSplitR.
        {
          iPureIntro.
          intros.
          specialize (HW_in_range s0 H).
          word.
        }
        iSplitR.
        {
          iPureIntro.
          word.
        }

        (* XXX: copy/pasted *)
        iApply "Hreplies".
        {
          iModIntro.
          iIntros (??????) "Hwand".
          iIntros (?).
          iApply "Hwand".
          iPureIntro.
          replace (uint.nat (word.add i 1%Z)) with (uint.nat i + 1) in H2 by word.
          word.
        }
        {
          iIntros.
          exfalso.
          replace (uint.nat (word.add i 1%Z)) with (uint.nat i + 1) in H by word.
          word.
        }
      }
    }
    { (* null pointer, don't do anything *)
      iModIntro.
      iApply "HΦ".
      iExists W, _.
      iFrame "∗#%".

      replace (uint.nat (word.add i 1%Z)) with (uint.nat i + 1) by word.
      iSplitR.
      {
        iPureIntro.
        intros.
        specialize (HW_in_range s0 H).
        word.
      }
      iSplitR.
      { iPureIntro. word. }

      (* XXX: copy/pasted *)
      iApply (big_sepL2_impl with "Hreplies").
      {
        iModIntro.
        iIntros (?????) "Hwand".
        iIntros (?).
        iApply "Hwand".
        iPureIntro.
        word.
      }
    }
  }
  iIntros "[Hi Hreplies_sl]".
  wp_pures.
  iNamed "Hi".
  wp_load.
  wp_if_destruct.
  { (* case: got enough replies to become leader *)
    destruct (decide (size W = 0)).
    {
      exfalso.
      rewrite e in Heqb1.
      replace (uint.Z (word.mul 2%Z 0%nat)) with (0)%Z in Heqb1; last first.
      { eauto. }
      word.
    }

    wp_apply (wp_Server__withLock with "[]").
    { repeat iExists _.
      iFrame "Hmu". iSplitR.
      { iExact "HmuInv". }
      iFrame "#".
    }
    iIntros (??) "HH".
    iRename "HP" into "HP_in".
    iNamed "HH".
    iClear "Hstate_sl".
    iNamed "Hvol".
    wp_pures.
    wp_loadField.
    wp_loadField.
    wp_if_destruct.
    { (* case: server has not advanced past newepoch, we become leader *)
      wp_loadField.
      wp_storeField.
      wp_storeField.
      wp_loadField.
      wp_storeField.
      wp_load.

      iNamed "Hi".
      iNamed "HlatestReply".
      wp_loadField.
      wp_storeField.
      wp_load.
      wp_loadField.
      wp_storeField.
      iDestruct (own_slice_small_sz with "Hreplies_sl") as "%Hreplies_sz".

      iModIntro.
      iExists _.
      rewrite sep_exist_r.
      instantiate (1:=paxosState.mk _ _ _ _ _).
      iExists _. simpl. iFrame.

      (* start ghost reasoning *)
      (* A few protocol steps *)
      iFrame "#".
      iIntros "Hghost".
      iNamed "Hghost".
      iMod (fupd_mask_subseteq (↑sysN)) as "Hmask".
      { solve_ndisj. }
      simpl.
      iDestruct (big_sepL2_length with "[$Hclerks_rpc]") as %Hlen.
      iMod (become_leader with "Hvote_inv Hacc_lbs Hlatest_prop Hvotes") as "HghostLeader".
      {
        intros ??.
        apply HW_in_range in H.
        simpl.
        word.
      }
      {
        enough (uint.Z (word.mul 2 (size W)) <= (2 * size W))%Z.
        { simpl in *. word. }
        rewrite word.unsigned_mul.
        rewrite /word.wrap /=.
        etransitivity.
        { apply Z.mod_le; word. }
        word.
      }
      iMod "Hmask".
      iDestruct (ghost_replica_helper1 with "Hghost") as %Hineq.
      iMod (ghost_replica_leader_init with "HghostLeader Hghost") as "[Hghost Hleader]".
      { simpl in *. word. }
      iModIntro.

      iSplitR "HΦ HΨ Hlocked Hreplies_sl HnumReplies Hreplies HreplyPostEscrow".
      {
        repeat iExists _. simpl.
        iFrame "∗#".
        iPureIntro.
        split_and!; try done.
        word.
      }
      wp_pures.
      wp_apply (release_spec with "[-HΦ HΨ]").
      {
        iFrame "HmuReplyInv Hlocked".
        iNext.
        iExists _, _.
        iFrame "∗#%".
      }
      wp_pures.
      iModIntro.
      by iApply "HΦ".
    }
    {
      wp_pures.
      iModIntro.
      iExists _.
      rewrite sep_exist_r.
      instantiate (1:=paxosState.mk _ _ _ _ _).
      iExists _. simpl.
      Opaque own_paxosState_ghost.
      iFrame "∗#".
      iIntros "$ !#".
      Transparent own_paxosState_ghost.
      wp_pures.
      wp_apply (release_spec with "[-HΦ HΨ]").
      {
        iFrame "HmuReplyInv Hlocked".
        iNext.
        iExists _, _.
        iFrame "∗#%".
      }
      wp_pures.
      iModIntro.
      by iApply "HΦ".
    }
  }
  { (* case: not enough replies *)
    wp_apply (release_spec with "[-HΦ HΨ]").
    {
      iFrame "HmuReplyInv Hlocked".
      iNext.
      iExists _, _.
      iFrame "∗#%".
    }
    wp_pures.
    iModIntro.
    by iApply "HΦ".
  }
Qed.

End becomeleader_proof.
