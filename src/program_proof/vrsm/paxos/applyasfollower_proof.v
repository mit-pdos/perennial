From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require paxos.
From Perennial Require Import urpc_proof urpc_spec.
From Perennial Require Export paxos.definitions paxos.withlock_proof.

Section applyasfollower_proof.

Context `{!heapGS Σ}.

Context `{!paxosG Σ}.
Context `{!paxosParams.t Σ}.
Import paxosParams.

Lemma wp_singleClerk__applyAsFollower ck γ γsrv σ args_ptr args :
  {{{
        "#His_ck" ∷ is_singleClerk ck γ γsrv ∗
        "Hargs" ∷ applyAsFollowerArgs.own args_ptr args ∗

        "#HP" ∷ □ Pwf args.(applyAsFollowerArgs.state) ∗
        "%Hσ_index" ∷ ⌜ length σ = (uint.nat args.(applyAsFollowerArgs.nextIndex))%nat ⌝ ∗
        "%Hghost_op_σ" ∷ ⌜ last σ.*1 = Some args.(applyAsFollowerArgs.state) ⌝ ∗
        "#Hprop" ∷ is_proposal (config:=γ.(s_hosts)) (N:=N) γ.(s_mp) args.(applyAsFollowerArgs.epoch) σ
  }}}
    singleClerk__applyAsFollower #ck #args_ptr
  {{{
        reply_ptr reply, RET #reply_ptr; applyAsFollowerReply.own reply_ptr reply (DfracOwn 1) ∗
                                                 □if (decide (reply.(applyAsFollowerReply.err) = (W64 0))) then
                                                   is_accepted_lb γsrv args.(applyAsFollowerArgs.epoch) σ
                                                 else
                                                   True
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  wp_apply (applyAsFollowerArgs.wp_Encode with "Hargs").
  iIntros (enc enc_sl) "[%Hargs_enc Hsl]".
  wp_pures.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rep_ptr) "Hrep".
  wp_pures.
  iNamed "His_ck".
  wp_loadField.
  iDestruct (own_slice_to_small with "Hsl") as "Hsl".
  iApply (wp_frame_wand with "[HΦ]").
  { iNamedAccu. }
  unfold is_paxos_host.
  iNamed "Hsrv".
  wp_apply (wp_ReconnectingClient__Call2 with "Hcl_rpc [] Hsl Hrep").
  { iFrame "#". }
  { (* Successful RPC *)
    iModIntro.
    iNext.
    unfold enterNewEpoch_spec.
    iExists _, _.
    iSplitR; first done.
    iSplit.
    {
      instantiate (1:=σ).
      unfold get_state.
      rewrite Hghost_op_σ.
      done.
   }
    iFrame "%#".

    iSplit.
    {
      iIntros "#Hacc_lb".
      iIntros (?) "%Henc_reply Hsl".
      iIntros (?) "Hrep Hrep_sl".
      wp_pures.
      wp_load.
      rewrite Henc_reply.
      wp_apply (applyAsFollowerReply.wp_Decode with "[$Hrep_sl]").
      { done. }
      iIntros (reply_ptr) "Hreply".
      iIntros "HΦ".
      iApply "HΦ".
      iFrame "∗".
      destruct (decide _).
      { iModIntro. iFrame "#". }
      done.
    }
    { (* Apply failed for some reason, e.g. node is not primary *)
      iIntros (? Hreply_err).
      iIntros (?) "%Henc_reply Hsl".
      iIntros (?) "Hrep Hrep_sl".
      wp_pures.
      wp_load.
      rewrite Henc_reply.
      wp_apply (applyAsFollowerReply.wp_Decode with "[$Hrep_sl]").
      { done. }
      iIntros (reply_ptr) "Hreply".
      iIntros "HΦ".
      iApply "HΦ".
      iFrame "∗".
      destruct (decide _).
      { exfalso. done. }
      { done. }
    }
  }
  { (* RPC error *)
    iIntros.
    wp_pures.
    destruct (bool_decide _) as [] eqn:X.
    {
      exfalso.
      apply bool_decide_eq_true in X.
      naive_solver.
    }
    wp_pures.

    wp_apply (wp_allocStruct).
    { repeat econstructor. }
    iIntros (reply_ptr) "Hreply".
    iNamed 1.
    iApply "HΦ".
    iDestruct (struct_fields_split with "Hreply") as "HH".
    iNamed "HH".

    iSplitL.
    {
      instantiate (1:=applyAsFollowerReply.mkC _).
      iFrame "∗#".
    }
    simpl.
    done.
  }
Qed.

Lemma wp_Server__applyAsFollower (s:loc) (args_ptr reply_ptr:loc) γ γsrv args init_reply σ Φ Ψ :
  is_Server s γ γsrv -∗
  applyAsFollowerArgs.own args_ptr args -∗
  applyAsFollowerReply.own reply_ptr init_reply (DfracOwn 1) -∗
  (∀ reply, Ψ reply -∗ applyAsFollowerReply.own reply_ptr reply (DfracOwn 1) -∗ Φ #()) -∗
  applyAsFollower_core_spec γ γsrv args σ Ψ -∗
  WP Server__applyAsFollower #s #args_ptr #reply_ptr {{ Φ }}
.
Proof.
  iIntros "#HisSrv Hpre Hreply HΦ HΨ".
  iNamed "Hpre".
  wp_call.
  wp_apply (wp_Server__withLock with "[$]").
  iIntros (??) "HH".
  iNamed "HH".
  wp_pures.
  iRename "HP" into "HP_in".
  iNamed "Hvol".
  wp_loadField.
  wp_loadField.
  wp_pures.
  iNamed "HΨ".
  wp_if_destruct.
  { (* case: s.epoch ≤ args.epoch *)
    wp_loadField.
    wp_loadField.
    wp_pures.
    wp_if_destruct.
    { (* case: s.acceptedEpoch = args.epoch *)
      wp_loadField.
      wp_loadField.
      wp_if_destruct.
      { (* case: s.nextIndex == len(s.log) ≤ args.nextIndex *)
        wp_loadField.
        wp_storeField.
        wp_loadField.
        wp_storeField.
        wp_storeField.
        iModIntro.
        iExists _.
        iSplitR "HΦ HΨ Hreply".
        {
          instantiate (1:=paxosState.mk _ _ _ _ _).
          repeat iExists _; simpl; iFrame "∗#".
        }
        iFrame "HP".

        (* start ghost reasoning *)
        (* use protocol lemma *)
        iIntros "Hghost".
        iNamed "Hghost".
        iMod (ghost_replica_accept_same_epoch with "Hghost Hprop") as "[%Heq Hghost]".
        { simpl. word. }
        { by rewrite Heqb0. }
        { simpl. rewrite Hσ_index. word. }
        simpl in Heq.
        iDestruct (ghost_replica_get_lb with "Hghost") as "#Hlb".
        simpl. iModIntro.
        iSplitR "HΦ HΨ Hreply".
        { repeat iExists _. simpl.
          rewrite Heqb0 Heq.
          destruct pst, isLeader; simpl in *; subst.
          { (* case: is leader; contradiction *)
            iExFalso.
            iDestruct (ghost_leader_proposal_ineq with "[Hprop] [$HleaderOnly]") as %Hineq.
            { simpl. iFrame "#". }
            exfalso. simpl in *.
            apply prefix_length in Hineq.
            word.
          }
          { (* not leader *)
            iFrame "Hghost #".
            iPureIntro.
            rewrite Hghost_op_σ.
            simpl.
            split_and!; try done; word.
          }
        }
        (* end ghost reasoning *)

        wp_pures.
        iModIntro.
        iApply ("HΦ" with "[HΨ]").
        {
          iLeft in "HΨ".
          iApply "HΨ".
          iFrame "#".
        }
        iFrame.
      }
      { (* case: args.nextIndex < s.nextIndex len(s.log) *)
        wp_storeField.
        iModIntro.
        iExists _.
        iSplitR "HΦ HΨ Hreply".
        {
          instantiate (1:=paxosState.mk _ _ _ _ _).
          repeat iExists _; simpl; iFrame "∗#".
        }

        simpl.
        iFrame "HP_in".
        (* start ghost reasoning *)
        iIntros "Hghost".
        iNamed "Hghost".
        assert (uint.Z (length log) >= uint.Z args.(applyAsFollowerArgs.nextIndex))%Z as Hineq.
        { word. }

        (* use protocol lemma *)
        iDestruct (ghost_replica_accept_same_epoch_old with "Hghost Hprop") as "#Hacc_lb".
        { simpl. word. }
        { simpl. rewrite Heqb0. done. }
        { simpl. word. }

        iModIntro.
        iSplitR "HΦ HΨ Hreply".
        { repeat iExists _. simpl. rewrite Heqb0.
          rewrite -Heqb0. 
          iFrame "∗ # %".
        }
        (* end ghost reasoning*)

        wp_pures.
        iApply ("HΦ" with "[HΨ]").
        {
          iLeft in "HΨ".
          iApply "HΨ".
          iFrame "#".
        }
        iModIntro. iFrame.
      }
    }
    { (* case acceptedEpoch ≠ args.epoch, which implies
         acceptedEpoch < args.epoch
       *)
      wp_loadField.
      wp_storeField.
      wp_loadField.
      wp_storeField.
      wp_loadField.
      wp_storeField.
      wp_loadField.
      wp_storeField.
      wp_storeField.
      wp_storeField.
      iModIntro.
      iExists _.
      iSplitR "HΦ HΨ Hreply".
      {
        instantiate (1:=paxosState.mk _ _ _ _ _).
        repeat iExists _; simpl; iFrame "∗#".
      }

      (* start ghost reasoning *)
      (* use protocol lemma *)
      iFrame "HP".
      iIntros "Hghost".
      iNamed "Hghost".
      iMod (ghost_replica_accept_new_epoch with "Hghost Hprop") as "Hghost".
      { simpl. word. }
      {
        simpl.
        destruct (decide (uint.nat pst.(paxosState.acceptedEpoch) =
                          uint.nat args.(applyAsFollowerArgs.epoch))).
        { exfalso. apply Heqb0. repeat f_equal. word. }
        { done. }
      }
      iDestruct (ghost_replica_get_lb with "Hghost") as "#Hlb".
      simpl.
      (* end ghost reasoning *)
      iModIntro.
      iSplitR "HΦ HΨ Hreply".
      { repeat iExists _. simpl.
        iFrame "Hghost # %".
        iPureIntro.
        split_and!; try done; try word.
      }
      (* end ghost reasoning*)

      wp_pures.
      iApply ("HΦ" with "[HΨ]").
      {
        iLeft in "HΨ".
        iApply "HΨ".
        iFrame "#".
      }
      iModIntro. iFrame.
    }
  }
  { (* case: s.epoch > args.epoch *)
    wp_storeField.
    iModIntro.
    iExists _.
    iSplitR "HΦ HΨ Hreply".
    {
      instantiate (1:=paxosState.mk _ _ _ _ _).
      repeat iExists _; simpl; iFrame "∗#".
    }
    Opaque own_paxosState_ghost.
    iFrame "HP_in".
    iIntros "$".
    Transparent own_paxosState_ghost.
    iModIntro.
    wp_pures.
    iNamed "HΨ".
    iRight in "HΨ".
    iModIntro.
    iApply ("HΦ" with "[HΨ]").
    2:{
      instantiate (1:=applyAsFollowerReply.mkC _).
      iFrame.
    }
    {
      iApply "HΨ".
      done.
    }
  }
Qed.

End applyasfollower_proof.
