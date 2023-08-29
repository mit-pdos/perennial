From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require mpaxos.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.mpaxos Require Export definitions.

Section applyasfollower_proof.

Context `{!heapGS Σ}.

Context (conf:list mp_server_names).
Context `{!mpG Σ}.

Lemma wp_singleClerk__applyAsFollower ck γ γsrv σ Q args_ptr args :
  {{{
        "#His_ck" ∷ is_singleClerk conf ck γ γsrv ∗
        "Hargs" ∷ applyAsFollowerArgs.own args_ptr args ∗

        "%Hσ_index" ∷ ⌜length σ = (int.nat args.(applyAsFollowerArgs.nextIndex) + 1)%nat⌝ ∗
        "%Hghost_op_σ" ∷ ⌜last σ = Some (args.(applyAsFollowerArgs.state), Q)⌝ ∗
        "%Hno_overflow" ∷ ⌜int.nat args.(applyAsFollowerArgs.nextIndex) < int.nat (word.add args.(applyAsFollowerArgs.nextIndex) 1)⌝ ∗
        "#Hprop" ∷ is_proposal γ args.(applyAsFollowerArgs.epoch) σ
  }}}
    singleClerk__applyAsFollower #ck #args_ptr
  {{{
        reply_ptr reply, RET #reply_ptr; applyAsFollowerReply.own reply_ptr reply 1 ∗
                                                 □if (decide (reply.(applyAsFollowerReply.err) = (U64 0))) then
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
  wp_apply (wp_ReconnectingClient__Call2 with "Hcl_rpc [] Hsl Hrep").
  {
    unfold is_mpaxos_host.
    iNamed "Hsrv".
    iFrame "#".
  }
  { (* Successful RPC *)
    iModIntro.
    iNext.
    unfold enterNewEpoch_spec.
    iExists _, _, _.
    iSplitR; first done.
    iSplit.
    {
      instantiate (1:=σ).
      unfold get_state.
      rewrite fmap_last.
      rewrite Hghost_op_σ.
      simpl.
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

Lemma wp_Server__applyAsFollower (s:loc) (args_ptr reply_ptr:loc) γ γsrv args init_reply σ Q Φ Ψ :
  is_Server conf s γ γsrv -∗
  applyAsFollowerArgs.own args_ptr args -∗
  applyAsFollowerReply.own reply_ptr init_reply 1 -∗
  (∀ reply, Ψ reply -∗ applyAsFollowerReply.own reply_ptr reply 1 -∗ Φ #()) -∗
  applyAsFollower_core_spec conf γ γsrv args σ Q Ψ -∗
  WP mpaxos.Server__applyAsFollower #s #args_ptr #reply_ptr {{ Φ }}
.
Proof.
  iIntros "#HisSrv Hpre Hreply HΦ HΨ".
  iNamed "Hpre".
  iNamed "HisSrv".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_loadField.
  wp_loadField.
  wp_pures.
  iNamed "HΨ".
  wp_if_destruct.
  { (* case: s.epoch ≤ args.epoch *)
    wp_storeField.
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
        wp_loadField.

        (* use protocol lemma *)
        iMod (ghost_replica_accept_same_epoch with "Hghost Hprop_lb Hprop_facts") as "[%Heq Hghost]".
        { word. }
        { by rewrite Heqb0. }
        { rewrite Hσ_index. word. }
        iDestruct (ghost_replica_get_lb with "Hghost") as "#Hlb".
        simpl.

        wp_apply (release_spec with "[-HΦ HΨ Hreply]").
        {
          iFrame "HmuInv Hlocked".
          iNext.
          iExists _,_,_,_,_,_.
          instantiate (1:=mkMPaxosState _ _ _).
          simpl.
          rewrite Heq.
          rewrite Heqb0.
          rewrite Hstate.
          iFrame "∗#%".
          iSplitL "HnextIndex".
          {
            iApply to_named.
            iExactEq "HnextIndex".
            f_equal.
            f_equal.
            rewrite Hσ_index.
            admit. (* TODO: nextIndex overflow *)
          }
          iPureIntro.
          split.
          { word. }
          done.
        }
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
        assert (int.Z (length st.(mp_log)) > int.Z args.(applyAsFollowerArgs.nextIndex))%Z as Hineq.
        { word. }
        wp_storeField.
        wp_loadField.

        (* use protocol lemma *)
        iDestruct (ghost_replica_accept_same_epoch_old with "Hghost Hprop_lb") as "#Hacc_lb".
        { word. }
        { rewrite Heqb0. done. }
        { word. }

        wp_apply (release_spec with "[-HΦ HΨ Hreply]").
        {
          iFrame "HmuInv Hlocked".
          iNext.
          iExists _,_,_,_,_,_.
          iFrame "HisLeader∗#%".
          done.
        }
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
      wp_loadField.

      (* use protocol lemma *)
      iMod (ghost_replica_accept_new_epoch with "Hghost Hprop_lb Hprop_facts") as "Hghost".
      { word. }
      {
        destruct (decide (int.nat st.(mp_acceptedEpoch) = int.nat args.(applyAsFollowerArgs.epoch))).
        {
          exfalso.
          replace (st.(mp_acceptedEpoch)) with (args.(applyAsFollowerArgs.epoch)) in Heqb0 by word.
          done.
        }
        {
          done.
        }
      }
      iDestruct (ghost_replica_get_lb with "Hghost") as "#Hlb".
      simpl.

      wp_apply (release_spec with "[-HΦ HΨ Hreply]").
      {
        iFrame "HmuInv Hlocked".
        iNext.
        iExists _,_,_,_,_,_.
        instantiate (1:=mkMPaxosState _ _ _).
        rewrite Hstate.
        simpl.
        iFrame "HisLeader∗#%".
        iSplitL "HnextIndex".
        {
          iApply to_named.
          iExactEq "HnextIndex".
          f_equal.
          f_equal.
          rewrite Hσ_index.
          admit. (* TODO: nextIndex overflow *)
        }
        iPureIntro.
        split.
        { word. }
        done.
      }
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
  }
  { (* case: s.epoch > args.epoch *)
    wp_storeField.
    wp_loadField.
    wp_apply (release_spec with "[-HΦ HΨ Hreply]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      iExists _, _, _, _, _, _.
      iFrame "∗#%".
    }
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
Admitted.

End applyasfollower_proof.
