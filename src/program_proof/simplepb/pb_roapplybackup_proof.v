From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.simplepb Require Import pb_ghost.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.program_proof.simplepb Require Import pb_definitions pb_marshal_proof pb_applybackup_proof.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.reconnectclient Require Import proof.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section pb_roapplybackup_proof.

Context `{!heapGS Σ}.
Context {pb_record:Sm.t}.

Notation OpType := (Sm.OpType pb_record).
Notation has_op_encoding := (Sm.has_op_encoding pb_record).
Notation compute_reply := (Sm.compute_reply pb_record).
Notation pbG := (pbG (pb_record:=pb_record)).
Notation get_rwops := (get_rwops (pb_record:=pb_record)).

Context `{!waitgroupG Σ}.
Context `{!pbG Σ}.

(* Clerk specs *)
Lemma wp_Clerk__RoApplyAsBackup γ γsrv ck args_ptr (epoch nextIndex:u64) opsfull :
  {{{
        "#Hck" ∷ is_Clerk ck γ γsrv ∗
        "#HepochLb" ∷ is_epoch_lb γsrv epoch ∗
        "#Hprop_lb" ∷ is_proposal_lb γ epoch opsfull ∗
        "#Hprop_facts" ∷ is_proposal_facts γ epoch opsfull ∗
        "%HnextIndex" ∷ ⌜length (get_rwops opsfull) = int.nat nextIndex⌝ ∗

        "#HargEpoch" ∷ readonly (args_ptr ↦[pb.RoApplyAsBackupArgs :: "epoch"] #epoch) ∗
        "#HargIndex" ∷ readonly (args_ptr ↦[pb.RoApplyAsBackupArgs :: "nextIndex"] #nextIndex)
  }}}
    Clerk__RoApplyAsBackup #ck #args_ptr
  {{{
        (err:u64), RET #err; □ if (decide (err = 0)) then
                               is_accepted_lb γsrv epoch opsfull
                             else True
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
  wp_apply (RoApplyAsBackupArgs.wp_Encode with "[]").
  {
    instantiate (1:=(RoApplyAsBackupArgs.mkC _ _)).
    iFrame "#".
  }
  iIntros (enc_args enc_args_sl) "(%Henc_args & Henc_args_sl)".
  wp_loadField.
  iDestruct (is_slice_to_small with "Henc_args_sl") as "Henc_args_sl".
  wp_apply (wp_frame_wand with "HΦ").
  rewrite is_pb_host_unfold.
  iNamed "Hsrv".
  wp_apply (wp_ReconnectingClient__Call2 with "Hcl_rpc [] Henc_args_sl Hrep").
  {
    iDestruct "Hsrv" as "(_ & _ & _ & _ & _ & $ & _)".
  }
  { (* Successful RPC *)
    iModIntro.
    iNext.
    unfold RoApplyAsBackup_spec.
    iExists _, _.
    iSplitR; first done.
    iFrame "#%".
    iSplit.
    { (* No error from RPC, Apply was accepted *)
      iIntros "#Hacc_lb".
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
      iModIntro.
      iFrame "#".
    }
    { (* Apply was rejected by the server (e.g. stale epoch number) *)
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

Local Ltac unseal := rewrite /own_Server_ghost_eph_f /own_Server_ghost_f /tc_opaque.

Lemma ghost_unsealed γ γsrv γeph st ops sealed :
  st.(server.sealed) = false →
  own_Server_ghost_eph_f st γ γsrv γeph -∗
  own_Server_ghost_f γ γsrv γeph st.(server.epoch) ops sealed -∗
  ⌜sealed = false⌝.
Proof.
  intros Hunsealed.
  unseal.
  iNamed 1.
  iNamed 1.
  rewrite Hunsealed.
  destruct sealed.
  {
    iExFalso. iNamed "Heph_sealed".
    by iDestruct (fmlist_ptsto_valid_2 with "Heph Heph_sealed") as %[Hbad _].
  }
  done.
Qed.

(* possibly update ephemeral points-to to later update accepted points to *)
Lemma roapplybackup_backup_eph_step γ γsrv γeph st ops_full' :
  st.(server.isPrimary) = false →
  st.(server.sealed) = false →
  int.nat st.(server.durableNextIndex) >= length (get_rwops ops_full') →
  is_proposal_lb γ st.(server.epoch) ops_full' -∗
  is_proposal_facts γ st.(server.epoch) ops_full' -∗
  own_Server_ghost_eph_f st γ γsrv γeph ==∗
  ∃ new_ops_full durable_ops_full,
  ⌜get_rwops new_ops_full = get_rwops st.(server.ops_full_eph)⌝ ∗
  ⌜length (get_rwops ops_full') <= length (get_rwops durable_ops_full)⌝ ∗
  is_accepted_lb γsrv st.(server.epoch) durable_ops_full ∗
  own_Server_ghost_eph_f (st <| server.ops_full_eph := new_ops_full |>) γ γsrv γeph ∗
  is_ephemeral_proposal_lb γeph st.(server.epoch) ops_full'
.
Proof.
  (* Two possibilities for a backup: ops_full' ⪰ ops_full_eph
     or ops_full' ⪯ ops_full_eph.
     In the first case, can update own_ephemeral and get the lb.
     In the second case, we can get the ephemeral_lb from the current
     own_ephemeral.
   *)
  intros Hbackup Hunsealed Hlen.
  iIntros "#Hprop_lb #Hprop_facts HghostEph".
  iEval (unseal) in "HghostEph".
  iNamed "HghostEph".
  rewrite Hbackup.
  rewrite Hunsealed.
  iDestruct (fmlist_ptsto_lb_comparable with "Hprop_lb Heph_prop_lb") as %[Hprefix|Hprefix].
  { (* case: ephemeral_proposal already has ops_full' in it *)
    iDestruct (fmlist_ptsto_get_lb with "Heph") as "#Heph_lb".
    iModIntro.
    iExists _, _; iFrame "∗#".
    iSplit; first done.
    iSplit; first iPureIntro.
    { word. }
    iSplitL.
    { repeat (iExists _). simpl. rewrite Hunsealed Hbackup. iFrame "∗#%". }
    by iApply fmlist_ptsto_lb_mono.
  }
  { (* case: need to grow ephemeral_proposal *)
    iDestruct (fmlist_ptsto_lb_agree with "Heph Hdurable_eph_lb") as %HdurablePrefix.
    iMod (fmlist_ptsto_update with "Heph") as "Heph".
    { done. }
    iDestruct (fmlist_ptsto_get_lb with "Heph") as "#Heph_lb".
    iModIntro.
    iExists _, _; iFrame "∗#".
    iSplitR; first iPureIntro.
    {
      (*
        durable ⪯ server.ops_eph ⪯ ops_full'
          and
        get_rwops ops_full' ⪯ get_rwops durable
       *)
      apply get_rwops_prefix in HdurablePrefix, Hprefix.
      symmetry. apply list_prefix_eq.
      { exact Hprefix. }
      assert (prefix (get_rwops ops_durable_full) (get_rwops ops_full')) as HdurableFull'.
      { by transitivity (get_rwops st.(server.ops_full_eph)). }
      apply list_prefix_eq in HdurableFull'; last first.
      { word. }
      apply prefix_length in HdurablePrefix, Hprefix.
      word.
    }
    iSplitR.
    { iPureIntro. word. }
    repeat iExists _.
    rewrite Hbackup Hunsealed.
    iDestruct "Hprop_facts" as "(_ & _ & $)".
    iFrame "∗#%".
    by iLeft.
  }
Qed.

(* possibly update accepted points-to *)
Lemma roapplybackup_ghost_step γ γsrv γeph epoch ops durable_ops ops_full' :
  length $ get_rwops durable_ops >= length $ get_rwops ops_full' →
  is_proposal_lb γ epoch ops_full' -∗
  is_proposal_facts γ epoch ops_full' -∗
  is_accepted_lb γsrv epoch durable_ops -∗
  is_ephemeral_proposal_lb γeph epoch ops_full' -∗
  own_Server_ghost_f γ γsrv γeph epoch ops false ==∗
  own_Server_ghost_f γ γsrv γeph epoch ops false ∗
  is_accepted_lb γsrv epoch ops_full'
.
Proof.
  intros HdurableLength.
  iIntros "#Hprop_lb #Hprop_facts #Hdur_acc_lb #Hnew_eph_lb Hghost".
  iEval unseal in "Hghost".
  iNamed "Hghost".
  subst.
  iDestruct (fmlist_ptsto_lb_comparable with "Hnew_eph_lb Heph_lb") as %[Hprefix|Hprefix].
  { (* case: already accepted ops_full' *)
    iDestruct (ghost_get_accepted_lb with "Hghost") as "#Hacc_lb".
    iModIntro.
    iSplitL.
    { repeat iExists _; iFrame "∗#%". done. }
    by iApply fmlist_ptsto_lb_mono.
  }
  { (* case: need to update accepted points-to, but show that the RWs are the same *)
    iDestruct (ghost_accept_lb_ineq with "Hdur_acc_lb Hghost") as %HdurablePrefix.
    iMod (ghost_accept with "Hghost Hprop_lb Hprop_facts") as "Hghost".
    { done. }
    { by apply prefix_length. }
    iMod (ghost_primary_accept with "Hprop_facts Hprop_lb Hprim") as "Hprim".
    { by apply prefix_length. }
    iDestruct (ghost_get_accepted_lb with "Hghost") as "#$".
    iModIntro. repeat iExists _; iFrame "∗#".
    iPureIntro.
    apply get_rwops_prefix in HdurablePrefix, Hprefix.
    apply list_prefix_eq.
    { done. }
    apply prefix_length in HdurablePrefix, Hprefix.
    word.
  }
Qed.

Lemma get_primary_witness γ γeph γsrv st :
  st.(server.isPrimary) = true →
  is_Primary_ghost_f γ γeph γsrv st -∗
  is_tok γsrv st.(server.epoch).
Proof.
  intros Hprim.
  rewrite /is_Primary_ghost_f /tc_opaque.
  by iNamed 1.
Qed.

Lemma roapplybackup_primary_step γ γsrv γeph ops_full' ops_old st :
st.(server.isPrimary) = true →
is_proposal_lb γ st.(server.epoch) ops_full' -∗
own_Server_ghost_eph_f st γ γsrv γeph -∗
own_Server_ghost_f γ γsrv γeph st.(server.epoch) ops_old false -∗
is_accepted_lb γsrv st.(server.epoch) ops_full'.
Proof.
  intros Hprim.
  iIntros "Hprop_lb HghostEph Hghost".
  unseal. iNamed "HghostEph". iNamed "Hghost".
  rewrite Hprim.
  subst.
  iDestruct "HprimaryOnly" as "[%Hbad|Hprimary]"; first by exfalso.
  iDestruct (get_primary_witness with "Hprimary") as "#Hwitness".
  { done. }
  iDestruct (ghost_propose_lb_valid with "Hwitness Hprim Hprop_lb") as %Hprefix.
  iDestruct (ghost_get_accepted_lb with "Hghost") as "#Hacc".
  by iApply fmlist_ptsto_lb_mono.
Qed.

Lemma roapplybackup_step γ γsrv γeph st ops_full' sm own_StateMachine :
  int.nat st.(server.durableNextIndex) >= length (get_rwops ops_full') →
  st.(server.sealed) = false →
  is_proposal_lb γ st.(server.epoch) ops_full' -∗
  is_proposal_facts γ st.(server.epoch) ops_full' -∗
  is_StateMachine sm own_StateMachine (own_Server_ghost_f γ γsrv γeph) -∗
  own_StateMachine st.(server.epoch) (get_rwops st.(server.ops_full_eph)) false
               (own_Server_ghost_f γ γsrv γeph) -∗
  own_Server_ghost_eph_f st γ γsrv γeph -∗
  £ 1 -∗
  |NC={⊤,⊤}=> wpc_nval ⊤ (
    own_StateMachine st.(server.epoch) (get_rwops st.(server.ops_full_eph)) false
                 (own_Server_ghost_f γ γsrv γeph) ∗
    (∃ new_ops_full,
    ⌜get_rwops new_ops_full = get_rwops st.(server.ops_full_eph)⌝ ∗
    own_Server_ghost_eph_f (st <| server.ops_full_eph := new_ops_full |> )γ γsrv γeph ∗
    is_accepted_lb γsrv st.(server.epoch) ops_full')
  )
.
Proof.
  intros HdurableLen Hunsealed.
  iIntros "#Hprop_lb #Hprop_facts HisSm Hstate HghostEph Hlc".
  iEval (rewrite /is_StateMachine /tc_opaque) in "HisSm".
  iNamed "HisSm".
  iApply ("HaccP" with "Hlc [-Hstate] Hstate").
  iIntros (ops_old ??) "Hghost".
  iDestruct (ghost_unsealed with "HghostEph Hghost") as "%Hunsealed2".
  { done. }
  subst.
  destruct (st.(server.isPrimary)) as [] eqn:HisPrimary.
  {
    iDestruct (roapplybackup_primary_step with "Hprop_lb HghostEph Hghost") as "#Hacc_lb".
    { done. }
    iFrame.
    iExists _; iFrame "∗#".
    by iPureIntro.
  }
  {
    iMod (roapplybackup_backup_eph_step with "Hprop_lb Hprop_facts HghostEph") as (??) "(%Hrws & %Hdurable & #Hacc_dur_lb & HghostEph & #Heph_lb)".
    1-3:done.
    iMod (roapplybackup_ghost_step with "Hprop_lb Hprop_facts Hacc_dur_lb Heph_lb Hghost") as "[Hghost #Hac_lb]".
    { done. }
    iFrame. iModIntro.
    iExists _.
    iFrame "∗#%".
  }
Qed.

Lemma wp_Server__RoApplyAsBackup (s:loc) (args_ptr:loc) γ γsrv args opsfull Φ Ψ :
  is_Server s γ γsrv -∗
  RoApplyAsBackupArgs.own args_ptr args -∗
  (∀ (err:u64), Ψ err -∗ Φ #err) -∗
  RoApplyAsBackup_core_spec γ γsrv args opsfull Ψ -∗
  WP pb.Server__RoApplyAsBackup #s #args_ptr {{ Φ }}
.
Proof.
  iIntros "#HisSrv Hpre HΦ HΨ".
  iNamed "Hpre".
  iNamed "HisSrv".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  wp_pures.

  (* for loop to wait for previous op to be applied *)
  wp_bind (For _ _ _).
  wp_forBreak.
  wp_pures.

  iNamed "Hown".
  iNamed "Hvol".

  wp_bind ((_ > _) && _ && _)%E.
  wp_apply (wp_and2 with "[Hargs_index Hsealed HdurableNextIndex HnextIndex Hargs_epoch Hepoch]"); first iNamedAccu; iNamed 1.
  { do 2 wp_loadField. wp_pures. iModIntro. iFrame. done. }
  { do 2 wp_loadField. wp_pures. iModIntro. iFrame. done. }
  { wp_loadField. wp_pures. iModIntro. iFrame. done. }

  wp_if_destruct.
  { (* loop again *)
    wp_pures.
    wp_loadField.
    wp_apply (wp_condWait with "[-HΦ HΨ Hargs_epoch Hargs_index]").
    {
      iFrame "#".
      iFrame "Hlocked".
      repeat (iExists _).
      iSplitR "HghostEph"; last iFrame.
      repeat (iExists _).
      (* time iFrame "∗#%". *)
      time (iFrame "∗"; iFrame "#"; iFrame "%").
    }
    iIntros "[Hlocked Hown]".
    wp_pures.
    iLeft.
    iModIntro.
    iSplitR; first done.
    iFrame.
  }
  (* done looping *)
  wp_pures.
  iModIntro.
  iRight.
  iSplitR; first done.
  wp_pures.

  iNamed "HΨ".
  wp_loadField.
  wp_loadField.
  wp_if_destruct.
  { (* return error: epoch changed *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ HΨ]").
    {
      iFrame "HmuInv Hlocked".
      repeat (iExists _).
      iSplitR "HghostEph"; last iFrame.
      repeat (iExists _).
      time (iFrame "∗"; iFrame "#"; iFrame "%").
    }
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iApply "HΨ".
    done.
  }

  wp_loadField.
  wp_if_destruct.
  { (* return error: sealed *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ HΨ]").
    {
      iFrame "HmuInv Hlocked".
      repeat (iExists _).
      iSplitR "HghostEph"; last iFrame.
      iNext.
      repeat (iExists _).
      rewrite Heqb0 Heqb1.
      time (iFrame "∗"; iFrame "#"; iFrame "%").
    }
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iApply "HΨ".
    done.
  }

  wp_loadField.
  wp_loadField.
  wp_pure1_credit "Hlc".
  wp_if_destruct.
  {
    exfalso.
    repeat rewrite not_and_r in Heqb.
    destruct Heqb as [|[|]].
    { word. }
    { rewrite Heqb0 in H. done. }
    { done. }
  }

  rewrite -Heqb0.
  iMod (roapplybackup_step with "Hprop_lb Hprop_facts HisSm Hstate HghostEph Hlc") as "HH".
  { word. }
  { done. }

  wp_pures.
  wp_bind (struct.loadF _ _ _).
  wp_apply (wpc_nval_elim_wp with "HH").
  { done. }
  { done. }
  wp_loadField.
  wp_pures.
  iIntros "[Hstate HH]".
  iDestruct "HH" as (?) "(%Hnewops & HghostEph & #Hacc_lb)".

  wp_apply (release_spec with "[-HΨ HΦ Hargs_epoch]").
  {
    iFrame "Hlocked HmuInv".
    iNext.
    repeat (iExists _).
    iSplitR "HghostEph"; last iFrame.
    repeat (iExists _).
    rewrite Heqb1.
    rewrite Hnewops.
    iFrame "∗#".
    iFrame "%".
  }
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iLeft in "HΨ".
  iApply "HΨ".
  iFrame "#".
Qed.

End pb_roapplybackup_proof.
