From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.simplepb Require Export pb_protocol.
From Perennial.program_proof.simplepb Require Import pb_marshal_proof.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.simplepb Require Import pb_definitions pb_increasecommit_proof.
From Perennial.program_proof.reconnectclient Require Import proof.
From iris.algebra Require Import mono_list.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section pb_setstate_proof.
Context `{!heapGS Σ}.
Context {params:pbParams.t}.
Import pbParams.
Import Sm.

Context `{!waitgroupG Σ}.
Context `{!pbG Σ}.

Lemma wp_Clerk__SetState γ γsrv ck args_ptr (prevEpoch epoch committedNextIndex:u64) opsfull snap :
  {{{
        "#Hck" ∷ is_Clerk ck γ γsrv ∗
        "#Hprop_lb" ∷ is_proposal_lb γ.(s_pb) epoch opsfull ∗
        "#Hprop_facts" ∷ is_proposal_facts γ.(s_pb) epoch opsfull ∗
        "#Hprop_facts_prim" ∷ is_proposal_facts_prim γ.(s_prim) epoch opsfull ∗
        "%Henc" ∷ ⌜has_snap_encoding snap (get_rwops opsfull)⌝ ∗
        "%Hno_overflow" ∷ ⌜length (get_rwops opsfull) = int.nat (length (get_rwops opsfull))⌝ ∗
        "#Hin_conf" ∷ is_in_config γ γsrv epoch ∗
        "%Hle" ∷ ⌜int.nat prevEpoch < int.nat epoch⌝ ∗
        "#HcommitFacts" ∷ commitIndex_facts γ prevEpoch committedNextIndex ∗
        "Hargs" ∷ SetStateArgs.own args_ptr (SetStateArgs.mkC epoch (length (get_rwops opsfull)) committedNextIndex snap)
  }}}
    Clerk__SetState #ck #args_ptr
  {{{
        (err:u64), RET #err;
        □(if (decide (err = U64 0)) then
            is_epoch_lb γsrv.(r_pb) epoch
          else
            True)
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rep) "Hrep".
  wp_pures.
  iNamed "Hck".
  wp_apply (SetStateArgs.wp_Encode with "[$Hargs]").
  iIntros (enc_args enc_args_sl) "(%Henc_args & Henc_args_sl & Hargs)".
  wp_loadField.
  iDestruct (own_slice_to_small with "Henc_args_sl") as "Henc_args_sl".
  wp_apply (wp_frame_wand with "HΦ").
  rewrite is_pb_rpcs_unfold.
  iNamed "Hsrv".
  wp_apply (wp_ReconnectingClient__Call2 with "Hcl_rpc [] Henc_args_sl Hrep").
  {
    iDestruct "Hsrv" as "[_ [$ _]]".
  }
  { (* Successful RPC *)
    iModIntro.
    iNext.
    unfold SetState_spec.
    iExists _, _.
    iSplitR; first done.
    iExists _.
    iSplitR; first done.
    iFrame "HcommitFacts".
    iSplitR; first done.
    simpl.
    iSplitR.
    { iPureIntro. word. }
    iFrame "Hprop_lb Hprop_facts Hprop_facts_prim #".
    iSplit.
    { (* No error from RPC, state was accepted *)
      iIntros "#Hepoch_lb".
      iIntros (?) "%Henc_rep Hargs_sl".
      iIntros (?) "Hrep Hrep_sl".
      wp_pures.
      wp_load.

      (* FIXME: separate lemma *)
      wp_call.
      rewrite Henc_rep.
      wp_apply (wp_ReadInt with "Hrep_sl").
      iIntros (?) "_".
      wp_pures.
      iModIntro.
      iIntros "HΦ".
      iApply "HΦ".
      iFrame "Hepoch_lb".
    }
    { (* SetState was rejected by the server (e.g. stale epoch number) *)
      iIntros (err) "%Herr_nz".
      iIntros.
      wp_pures.
      wp_load.
      wp_call.
      rewrite H.
      wp_apply (wp_ReadInt with "[$]").
      iIntros.
      wp_pures.
      iModIntro.
      iIntros "HΦ".
      iApply "HΦ".
      iFrame.
      iModIntro.
      destruct (decide _).
      {
        exfalso. done.
      }
      {
        done.
      }
    }
  }
  { (* RPC error *)
    iIntros.
    wp_pures.
    wp_if_destruct.
    {
      iModIntro.
      iIntros "HΦ".
      iApply "HΦ".
      destruct (decide (_)).
      { exfalso. done. }
      { done. }
    }
    { exfalso. done. }
  }
Qed.

Lemma get_epoch_eph γ γsrv st :
  own_Server_ghost_eph_f st γ γsrv -∗
  is_epoch_lb γsrv.(r_pb) st.(server.epoch)
.
Proof.
  rewrite /own_Server_ghost_eph_f /tc_opaque. by iNamed 1.
Qed.

Lemma setstate_primary_eph_step γ γsrv epoch isPrimary canBecomePrimary committedNextIndex epoch' ops ops' :
  int.nat epoch < int.nat epoch' →
  is_proposal_lb γ.(s_pb) epoch' ops' -∗
  is_proposal_facts_prim γ.(s_prim) epoch' ops' -∗
  own_tok γsrv.(r_prim) epoch' -∗
  own_Primary_ghost_f γ γsrv isPrimary canBecomePrimary epoch committedNextIndex ops -∗
  own_Primary_ghost_f γ γsrv true false epoch' committedNextIndex ops'
.
Proof.
  iIntros (Hepoch) "#Hprop_lb #Hprim_facts Htok_in".
  rewrite /own_Primary_ghost_f /tc_opaque.
  iNamed 1. iFrame "∗#".
Qed.

Lemma lease_invalid γ epoch leaseValid leaseExpiration :
  is_Server_lease_resource γ epoch leaseValid leaseExpiration -∗
  is_Server_lease_resource γ epoch false leaseExpiration
.
Proof.
  iNamed 1. repeat iExists _. by iFrame "#".
Qed.

Lemma setstate_eph_step γ γsrv st epoch' ops' :
  int.nat st.(server.epoch) < int.nat epoch' →
  is_proposal_lb γ.(s_pb) epoch' ops' -∗
  is_proposal_facts γ.(s_pb) epoch' ops' -∗
  is_proposal_facts_prim γ.(s_prim) epoch' ops' -∗
  is_in_config γ γsrv epoch' -∗
  own_tok γsrv.(r_prim) epoch' -∗
  own_Server_ghost_eph_f st γ γsrv ==∗
  (is_epoch_lb γsrv.(r_pb) epoch' -∗
   is_accepted_lb γsrv.(r_pb) epoch' ops' -∗
   own_Server_ghost_eph_f (st <| server.ops_full_eph := ops' |> <| server.epoch := epoch' |>
                              <| server.sealed := false |> <| server.isPrimary := false |>
                              <| server.canBecomePrimary := true |>
                              <| server.leaseValid := false |>
                         ) γ γsrv)
.
Proof.
  intros HnewEpoch.
  iIntros "#Hprop_lb #Hprop_facts #Hprim_facts #Hin_conf' Htok Hghost".
  rewrite /own_Server_ghost_eph_f /tc_opaque.
  iNamed "Hghost".
  iModIntro. iIntros. repeat iExists _.
  iFrame "∗#".
  simpl.
  iDestruct (lease_invalid with "[$]") as "$".
  iFrame "#".
  iSplitL.
  { iApply (setstate_primary_eph_step with "Hprop_lb Hprim_facts Htok Hprimary"). done. }
  iSplitL.
  {
    iModIntro. iIntros (???) "?". iApply "Hcommit_fact".
    2: { iPureIntro. right. word. }
    iPureIntro. word.
  }
  iSplitL.
  2:{ iFrame "%". }
  iDestruct ("Hcommit_fact" with "[] [] Hprop_lb Hprop_facts") as "%".
  { iPureIntro. word. }
  { iPureIntro. right. done. }
  iApply (fmlist_ptsto_lb_mono with "Hprop_lb").
  done.
Qed.

Lemma setstate_step γ γsrv epoch ops sealed epoch' opsfull':
  int.nat epoch < int.nat epoch' →
  is_proposal_lb γ.(s_pb) epoch' opsfull' -∗
  is_proposal_facts γ.(s_pb) epoch' opsfull' -∗
  is_proposal_facts_prim γ.(s_prim) epoch' opsfull' -∗
  is_in_config γ γsrv epoch' -∗
  own_Server_ghost_f γ γsrv epoch ops sealed ={⊤∖↑pbAofN}=∗
  own_Server_ghost_f γ γsrv epoch' (get_rwops opsfull') false ∗
  is_epoch_lb γsrv.(r_pb) epoch' ∗
  is_accepted_lb γsrv.(r_pb) epoch' opsfull' ∗
  own_tok γsrv.(r_prim) epoch'
.
Proof.
  intros HnewEpoch.
  iIntros "#? #? #? #? Hghost".
  iNamed "Hghost".
  iMod (ghost_accept_and_unseal with "Hghost [$] [$]") as "Hghost".
  { done. }

  iDestruct (ghost_get_epoch_lb with "Hghost") as "#Hepoch_lb".
  iDestruct (ghost_get_accepted_lb with "Hghost") as "#Hacc_lb".
  iDestruct (ghost_primary_accept_new_epoch with "Hprim_escrow") as "[Hprim_escrow $]".
  { done. }
  iSplitL.
  {
    iExists _.
    iFrame "∗#".
    iPureIntro. done.
  }
  iModIntro.
  iCombine "Hepoch_lb Hacc_lb" as "HH".
  iExact "HH".
Qed.

Lemma wp_Server__SetState γ γsrv s args_ptr args opsfull Φ Ψ :
  is_Server s γ γsrv -∗
  SetStateArgs.own args_ptr args -∗
  (∀ (err:u64), Ψ err -∗ Φ #err) -∗
  SetState_core_spec γ γsrv args opsfull Ψ -∗
  WP pb.Server__SetState #s #args_ptr {{ Φ }}
.
Proof.
  iIntros "#His_srv Hargs HΦ HΨ".
  iNamed "His_srv".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "[$HmuInv]").
  iIntros "[Hlocked Hown]".
  wp_pures.
  iNamed "Hown".
  iNamed "Hargs".
  iNamed "Hvol".
  wp_loadField.
  wp_loadField.
  wp_if_destruct.
  { (* stale epoch *)
    wp_loadField.
    unfold SetState_core_spec.
    iDestruct "HΨ" as (?) "(_ & _ & _ & _ & _ & _ & HΨ)".
    iRight in "HΨ".
    wp_apply (release_spec with "[-HΨ HΦ]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      repeat (iExists _).
      iSplitR "HghostEph"; last iFrame.
      repeat (iExists _).
      by iFrame "∗#".
    }
    wp_pures.
    iApply "HΦ".
    iRight in "HΨ".
    iApply "HΨ".
    done.
  }
  { (* successfully set the state *)
    wp_loadField.
    wp_loadField.
    wp_if_destruct.
    { (* state has been set previously. Use is_prop_lb to get agreement. *)
      wp_loadField.
      iDestruct (get_epoch_eph with "HghostEph") as "#Heph_lb".
      iDestruct "HΨ" as (?) "(_ & _ & _ & _ & _ & _ & _ & _ & HΨ)".
      iLeft in "HΨ".
      wp_apply (release_spec with "[-HΨ HΦ]").
      {
        iFrame "HmuInv Hlocked".
        iNext.
        repeat (iExists _).
        iSplitR "HghostEph"; last iFrame.
        repeat (iExists _).
        by iFrame "∗#".
      }
      wp_pures.
      iApply "HΦ".
      iApply "HΨ".
      by rewrite Heqb0.
    }
    iAssert (_) with "HisSm" as "#HisSm2".
    iEval (rewrite /is_StateMachine /tc_opaque) in "HisSm2".
    iNamed "HisSm2".
    wp_storeField.
    wp_storeField.
    wp_loadField.
    wp_storeField.
    wp_storeField.
    wp_storeField.
    wp_loadField.
    wp_storeField.
    wp_loadField.
    wp_loadField.
    wp_loadField.
    wp_loadField.
    wp_loadField.

    iDestruct "HΨ" as (prevEpoch) "(%Henc_snap &  %Hlen_nooverflow & %Hle & #Hprop_lb & #Hprop_facts & #Hprim_facts & #Hin_conf & #HcommitFacts & HΨ)".
    replace (args.(SetStateArgs.nextIndex)) with (U64 (length (get_rwops opsfull))) by word.

    assert (int.nat st.(server.epoch) < int.nat args.(SetStateArgs.epoch)) as HepochIneq.
    (* FIXME: should be trivial, almost `word` proof. Have (a ≠ b) and ¬(a < b) *)
    {
      assert (int.nat st.(server.epoch) ≠ int.nat args.(SetStateArgs.epoch)).
      { intros ?. apply Heqb0.
        repeat f_equal. word. }
      word.
    }

    unfold is_SetStateAndUnseal_fn.
    wp_apply ("HsetStateSpec" with "[$Hstate]").
    {
      iSplitR.
      { iPureIntro. word. }
      iSplitR; first done.
      iFrame "Hargs_state_sl".
      iIntros "Hghost".
      iMod (setstate_step with "[$] [$] [$] [$] Hghost") as "[$ H]".
      { done. }
      iExact "H".
    }
    iIntros "(Hstate & #Hepoch_lb & #Hacc_lb & Htok)".
    iMod (setstate_eph_step with "Hprop_lb Hprop_facts Hprim_facts Hin_conf Htok HghostEph") as "HghostEph".
    { done. }
    iDestruct ("HghostEph" with "Hepoch_lb Hacc_lb") as "HghostEph".

    wp_pures.
    wp_loadField.

    (* signal all opApplied condvars *)
    wp_apply (wp_MapIter with "HopAppliedConds_map HopAppliedConds_conds").
    { iFrame "HopAppliedConds_conds". }
    { (* prove one iteration of the map for loop *)
      iIntros.
      iIntros (?) "!# [_ #Hpre] HΦ".
      wp_pures.
      wp_apply (wp_condSignal with "Hpre").
      iApply "HΦ".
      iFrame "#".
      instantiate (1:=(λ _ _, True)%I).
      done.
    }
    iIntros "(HopAppliedConds_map & _ & _)".
    wp_loadField.
    wp_apply (wp_condBroadcast with "[]").
    { done. }
    wp_apply (wp_NewMap).
    iIntros (opAppliedConds_loc_new) "Hmapnew".
    wp_storeField.

    wp_loadField.
    wp_apply (release_spec with "[-HΨ HΦ Hargs_committed_next_index]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      repeat (iExists _).
      iSplitR "HghostEph"; last iFrame.
      repeat (iExists _).
      iFrame "∗ HisSm #%".
      simpl.
      iSplitR.
      { iApply big_sepM_empty. done. }
      iSplitR; first by iLeft.
      iPureIntro.
      unfold no_overflow.
      word. (* FIXME: how to avoid needing to unfold? *)
    }
    wp_pures.
    wp_loadField.
    wp_apply (wp_Server__IncreaseCommit with "[] [-] []").
    { repeat iExists _; iFrame "#". }
    2:{
      instantiate (1:=(λ _, True)%I).
      iNamed "HcommitFacts".
      repeat iExists _; iFrame "Hcommit_fact #".
      iDestruct (mono_nat_lb_own_le with "Hepoch_lb") as "$".
      { word. }
      iPureIntro. rewrite fmap_length in HcommitLen.
      word.
    }
    iIntros "_".

    wp_pures.
    iLeft in "HΨ".
    iApply "HΦ".
    iApply "HΨ".
    {
      done.
    }
  }
Qed.

End pb_setstate_proof.
