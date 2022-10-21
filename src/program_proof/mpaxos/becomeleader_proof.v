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
    wp_loadField.
    wp_apply (release_spec with "[-HΦ]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      iExists _,_,_,_,_,_.
      iFrame "∗#%".
      iFrame "HleaderOnly".
    }
    wp_pures.
    iModIntro.
    by iApply "HΦ".
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
                    "#Hreplies" ∷ ([∗ list] i ↦ reply_ptr ; γsrv' ∈ reply_ptrs ; conf,
                    ⌜reply_ptr = null⌝ ∨ (∃ reply, readonly (enterNewEpochReply.own reply_ptr reply 1) ∗
                                              □(if decide (reply.(enterNewEpochReply.err) = (U64 0)) then
                                                enterNewEpoch_post conf γ γsrv' reply newepoch
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
      iMod (readonly_alloc_1 with "Hreply") as "Hreply".
      wp_apply (release_spec with "[-]").
      {
        iFrame "# Hlocked".
        iNext.
        iExists _, _.
        iFrame "∗".
        iApply to_named.
        iDestruct (big_sepL2_insert_acc with "Hreplies")  as "[_ Hreplies2]".
        { done. }
        { done. }
        iDestruct ("Hreplies2" $! reply_ptr x2 with "[Hreply]") as "Hreplies3".
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

  set (I:=λ (i:u64), (
                 ∃ (W: gset nat) (latestReply_loc:loc),
                 "%HW_in_range" ∷ ⌜∀ s, s ∈ W → s < int.nat i⌝ ∗
                 "%HW_size_nooverflow" ∷ ⌜(size W) ≤ int.nat i⌝ ∗
                 "HnumSuccesses" ∷ numSuccesses_ptr ↦[uint64T] #(U64 (size W)) ∗
                 "HlatestReply_loc" ∷ latestReply_ptr ↦[ptrT] #latestReply_loc ∗
                 if (decide (size W = 0)) then
                   True
                 else
                   ∃ latestReply latestLog,
                  "#HlatestReply" ∷ readonly (enterNewEpochReply.own latestReply_loc latestReply 1) ∗
                  "%Hlatestlog" ∷ ⌜latestReply.(enterNewEpochReply.state) = get_state latestLog⌝ ∗
                  "%HlatestlogLen" ∷ ⌜int.nat latestReply.(enterNewEpochReply.nextIndex) = length latestLog⌝ ∗
                  "%HlatestEpoch_ineq" ∷ ⌜int.nat latestReply.(enterNewEpochReply.acceptedEpoch) < int.nat newepoch⌝ ∗
                  "#Hlatest_prop_lb" ∷ is_proposal_lb γ latestReply.(enterNewEpochReply.acceptedEpoch) latestLog ∗
                  "#Hacc_lbs" ∷ (□ [∗ list] s ↦ γsrv' ∈ conf, ⌜s ∈ W⌝ →
                                        is_accepted_upper_bound γsrv' latestLog
                                                                latestReply.(enterNewEpochReply.acceptedEpoch)
                                                                newepoch
                                )
      )%I).

  wp_apply (wp_forSlice (V:=loc) I _ _ _ _ _ reply_ptrs with "[] [HnumSuccesses HlatestReply Hreplies_sl]").
  2: {
    iFrame "Hreplies_sl".
    iExists ∅, null.
    rewrite size_empty.
    simpl.
    iFrame.
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
      iDestruct (big_sepL2_lookup_acc with "Hreplies") as "[#Hreply_post _]".
      { done. }
      { done. }
      iDestruct "Hreply_post" as "[%Hbad|#Hreply_post]".
      {
        exfalso. rewrite Hbad in Heqb1. done.
      }
      iDestruct "Hreply_post" as (?) "[#Hreply Hpost]".
      iMod (readonly_load with "Hreply") as (?) "Hreplyq".
      iNamed "Hreplyq".
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
            destruct (decide (W = ∅)).
            {
              done.
            }
            assert (size W = 0).
            { admit. } (* FIXME: overflow reasoning about size W *)
            apply size_empty_inv in H.
            by apply leibniz_equiv.
          }
          iModIntro.
          iApply "HΦ".

          iExists {[ int.nat i ]}, x.
          iSplitR.
          {
            iPureIntro.
            intros.
            apply elem_of_singleton_1 in H.
            rewrite H.
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
          rewrite Heqb.
          iDestruct "Hpost" as "#Hpost".
          destruct (decide (_)); last first.
          { exfalso. done. }
          iDestruct "Hpost" as (?) "(%Hepoch_ineq & %Hlog & %Hlen & #Hacc_ub & #Hprop_lb & #Hprop_facts)".
          iExists reply, log.
          iFrame "Hreply".
          iFrame "#%".
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
          { exfalso. rewrite e in Heqb2. done. }
          iNamed "Hi".
          iMod (readonly_load with "HlatestReply") as (?) "HlatestReply2".
          iRename "Hreply_acceptedEpoch" into "Hreply_acceptedEpoch2".
          iRename "Hreply_nextIndex" into "Hreply_nextIndex2".
          iClear "Hreply_err Hreply_ret Hreply_ret_sl".
          iNamed "HlatestReply2".
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

            iExists (W ∪ {[ int.nat i ]}), x.

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
              destruct (decide (int.nat i ∈ W)).
              {
                exfalso.
                specialize (HW_in_range (int.nat i) e).
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
            replace (word.add (size W) 1) with (U64 (size W + 1)%nat) by word.
            iFrame.
            destruct (decide (size W + 1 = 0)).
            { done. }

            iDestruct "Hpost" as "#Hpost".
            destruct (decide (_)); last first.
            { exfalso. done. }
            iDestruct "Hpost" as (?) "(%Hepoch_ineq & %Hlog & %Hlen & #Hacc_ub & #Hprop_lb & #Hprop_facts)".
            iExists reply, log.
            iFrame "Hreply Hprop_lb %".
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
                iExists (W ∪ {[ int.nat i ]}), x.
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
                  destruct (decide (int.nat i ∈ W)).
                  {
                    exfalso.
                    specialize (HW_in_range (int.nat i) e).
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
                replace (word.add (size W) 1) with (U64 (size W + 1)%nat) by word.
                iFrame.
                destruct (decide (size W + 1 = 0)).
                { done. }

                iDestruct "Hpost" as "#Hpost".
                destruct (decide (_)); last first.
                { exfalso. done. }
                iDestruct "Hpost" as (?) "(%Hepoch_ineq & %Hlog & %Hlen & #Hacc_ub & #Hprop_lb & #Hprop_facts)".
                iExists reply, log.
                iFrame "Hreply Hprop_lb %".
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
                  iDestruct (is_proposal_lb_compare with "Hprop_lb Hlatest_prop_lb") as "%Hpre".
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
                iExists (W ∪ {[ int.nat i ]}), _.
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
                  destruct (decide (int.nat i ∈ W)).
                  {
                    exfalso.
                    specialize (HW_in_range (int.nat i) e).
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
                replace (word.add (size W) 1) with (U64 (size W + 1)%nat) by word.
                iFrame.
                destruct (decide (size W + 1 = 0)).
                { done. }
                iExists _, _; iFrame "#%".

                iDestruct "Hpost" as "#Hpost".
                destruct (decide (_)); last first.
                { exfalso. done. }
                iDestruct "Hpost" as (?) "(%Hepoch_ineq & %Hlog & %Hlen & #Hacc_ub & #Hprop_lb & #Hprop_facts)".
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

                  iDestruct (is_proposal_lb_compare with "Hlatest_prop_lb Hprop_lb") as %Hpre.
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
            iExists (W ∪ {[ int.nat i ]}), _.
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
              destruct (decide (int.nat i ∈ W)).
              {
                exfalso.
                specialize (HW_in_range (int.nat i) e).
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
            replace (word.add (size W) 1) with (U64 (size W + 1)%nat) by word.
            iFrame.
            destruct (decide (size W + 1 = 0)).
            { done. }
            iExists _, _; iFrame "#%".

            iDestruct "Hpost" as "#Hpost".
            destruct (decide (_)); last first.
            { exfalso. done. }
            iDestruct "Hpost" as (?) "(%Hepoch_ineq & %Hlog & %Hlen & #Hacc_ub & #Hprop_lb & #Hprop_facts)".
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
                  destruct (decide (int.nat reply.(enterNewEpochReply.acceptedEpoch) = int.nat latestReply.(enterNewEpochReply.acceptedEpoch))).
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
        iPureIntro.
        replace (int.nat (word.add i 1%Z)) with (int.nat i + 1) by word.
        split.
        {
          intros.
          specialize (HW_in_range s0 H).
          word.
        }
        {
          word.
        }
      }
    }
    { (* null pointer, don't do anything *)
      iModIntro.
      iApply "HΦ".
      iExists W, _.
      iFrame "∗#%".
      iPureIntro.
      replace (int.nat (word.add i 1%Z)) with (int.nat i + 1) by word.
      split.
      {
        intros.
        specialize (HW_in_range s0 H).
        word.
      }
      {
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
    wp_loadField.
    destruct (decide (size W = 0)).
    {
      exfalso.
      rewrite e in Heqb1.
      replace (int.Z (word.mul 2%Z 0%nat)) with (0)%Z in Heqb1; last first.
      { eauto. }
      word.
    }

    wp_apply (acquire_spec with "HmuInv").
    iIntros "[Hlocked2 Hown]".
    wp_pures.
    iNamed "Hown".
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
      iMod (readonly_load with "HlatestReply") as (?) "HlatestReply2".
      iNamed "HlatestReply2".
      wp_loadField.
      wp_storeField.
      wp_load.
      wp_loadField.
      wp_storeField.
      wp_loadField.

      iClear "Hstate_sl Hclerks_sl Hclerks_rpc HisApplyFn Hinv".
      iNamed "Hown".
      rewrite Hlatestlog.
      (* A few protocol steps *)
      iMod (readonly_alloc (is_slice_small state_sl1 byteT 1 (get_state latestLog))
                           (Φ:=(λ q, (is_slice_small state_sl1 byteT q (get_state latestLog))))
                           q0 with "Hreply_ret_sl") as "#Hst_sl".
      iApply fupd_wp.
      iMod (fupd_mask_subseteq (↑sysN)) as "Hmask".
      { set_solver. }
      iMod (become_leader with "Hacc_lbs []") as "HghostLeader".
      { admit. (* FIXME: word.mul overflow with size W *) }
      { admit. } (* FIXME: votes *)
      iMod "Hmask".
      iDestruct (ghost_replica_helper1 with "Hghost") as %Hineq.
      iDestruct (ghost_leader_get_proposal with "HghostLeader") as "#[Hprop_lb Hprop_facts]".
      iMod (ghost_replica_accept_new_epoch with "Hghost Hprop_lb Hprop_facts") as "Hghost".
      { simpl. word. }
      { simpl. word. }
      iModIntro.

      wp_apply (release_spec with "[-HΦ Hlocked Hreplies_sl HnumReplies]").
      {
        iFrame "HmuInv Hlocked2".
        iNext.
        iExists _, _, _, _, _, _.
        instantiate (1:=mkMPaxosState _ _ _).
        simpl.
        iFrame "HisLeader ∗".
        iSplitL "HnextIndex".
        {
          iApply to_named.
          iExactEq "HnextIndex".
          f_equal.
          f_equal.
          f_equal. (* XXX: this looks like it has no effect, but actually strips off a base_lit *)
          word.
        }
        iFrame "#".
        iSplitR.
        { iPureIntro. word. }
        iSplitR.
        { iPureIntro. word. }
        done.
      }
      wp_pures.
      wp_apply (release_spec with "[-HΦ]").
      {
        iFrame "HmuReplyInv Hlocked".
        iNext.
        iExists _, _.
        iFrame "∗#".
      }
      wp_pures.
      iModIntro.
      by iApply "HΦ".
    }
    {
      wp_pures.
      wp_loadField.
      wp_apply (release_spec with "[-HΦ Hlocked Hreplies_sl HnumReplies]").
      {
        iFrame "HmuInv Hlocked2".
        iNext.
        iExists _, _, _, _, _, _.
        iFrame "∗#".
      }
      wp_pures.
      wp_apply (release_spec with "[-HΦ]").
      {
        iFrame "HmuReplyInv Hlocked".
        iNext.
        iExists _, _.
        iFrame "∗#".
      }
      wp_pures.
      iModIntro.
      by iApply "HΦ".
    }
  }
  { (* case: not enough replies *)
    wp_apply (release_spec with "[-HΦ]").
    {
      iFrame "HmuReplyInv Hlocked".
      iNext.
      iExists _, _.
      iFrame "∗#".
    }
    wp_pures.
    iModIntro.
    by iApply "HΦ".
  }
Admitted.

End becomeleader_proof.
