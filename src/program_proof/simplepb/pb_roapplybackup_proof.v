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

Lemma ghost_unsealed γ γsrv γeph st epoch ops sealed :
  st.(server.sealed) = false →
  own_Server_ghost_eph_f st γ γsrv γeph -∗
  own_Server_ghost_f γ γsrv γeph epoch ops sealed →
  ⌜sealed = false⌝.
Proof.
Admitted.

Lemma roapplybackup_backup_eph_step γ γsrv γeph st ops_full' :
  st.(server.isPrimary) = false →
  st.(server.sealed) = false →
  int.nat st.(server.durableNextIndex) >= length (get_rwops ops_full') →
  is_proposal_lb γ st.(server.epoch) ops_full' -∗
  is_proposal_facts γ st.(server.epoch) ops_full' -∗
  own_Server_ghost_eph_f st γ γsrv γeph ==∗
  ∃ new_ops_full durable_ops_full,
  ⌜get_rwops new_ops_full = get_rwops st.(server.ops_full_eph)⌝ ∗
  ⌜get_rwops ops_full' = get_rwops durable_ops_full⌝ ∗
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
Admitted.

Lemma roapplybackup_ghost_step γ γsrv γeph epoch ops durable_ops ops_full' :
  get_rwops durable_ops = get_rwops ops_full' →
  is_proposal_lb γ epoch ops_full' -∗
  is_proposal_facts γ epoch ops_full' -∗
  is_accepted_lb γsrv epoch durable_ops -∗
  is_ephemeral_proposal_lb γeph epoch ops_full' -∗
  own_Server_ghost_f γ γsrv γeph epoch ops false ==∗
  own_Server_ghost_f γ γsrv γeph epoch ops false ∗
  is_accepted_lb γsrv epoch ops_full'
.
Proof.
Admitted.

Lemma roapplybackup_primary_step γ γsrv γeph ops_full' ops_old st :
st.(server.isPrimary) = true →
is_proposal_lb γ st.(server.epoch) ops_full' -∗
own_Server_ghost_eph_f st γ γsrv γeph -∗
own_Server_ghost_f γ γsrv γeph st.(server.epoch) ops_old false -∗
is_accepted_lb γsrv st.(server.epoch) ops_full'.
Proof.
Admitted.

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

(*
  iDestruct "Heph_prop_lb" as "#Heph_prop_lb".
  iAssert ((|NC={⊤,⊤}=>
           wpc_nval ⊤
             (own_StateMachine args.(RoApplyAsBackupArgs.epoch) (get_rwops opsfull_ephemeral) false
                (own_Server_ghost γ γsrv γeph) ∗
                ((is_accepted_lb γsrv args.(RoApplyAsBackupArgs.epoch) opsfull) ∗
                  (∃ new_opsfull_ephemeral, ⌜get_rwops new_opsfull_ephemeral = get_rwops opsfull_ephemeral⌝ ∗
                  ⌜if isPrimary then new_opsfull_ephemeral = opsfull_ephemeral else True⌝ ∗
                  (if isPrimary then True else is_proposal_lb γ args.(RoApplyAsBackupArgs.epoch) new_opsfull_ephemeral) ∗
                  is_proposal_valid γ new_opsfull_ephemeral ∗
                  own_ephemeral_proposal γeph args.(RoApplyAsBackupArgs.epoch) new_opsfull_ephemeral)
             ))

           )%I) with "[Hlc Heph Hstate]" as "HH".
  {
  (* Want to establish:
     is_ephemeral_proposal_lb γeph args.(ApplyAsBackupArgs.epoch) opsfull
     This requires us to know that opsfull_ephemeral ⪯ opsfull.
     We will establish this using accP.
   *)
    destruct isPrimary.
    { (* case: is primary. *)
      iAssert (_) with "HprimaryOnly" as "Hprim2".
      iEval (rewrite /is_possible_Primary /tc_opaque) in "Hprim2".
      iMod ("HaccP" with "Hlc [Heph] Hstate") as "$"; last first.
      {
        (* PERF *)
        (* time done. *) (* takes 5 seconds*)
        (* time (iModIntro; done). *) (* takes 0.2 seconds, still a lot longer than below *)
        time (iModIntro; iApply True_intro; iAccu). }
      iIntros (???) "Hghost".
      iNamed "Hghost".
      iNamed "Hprim2".
      iDestruct (ghost_propose_lb_valid with "Htok_used_witness Hprim Hprop_lb") as %Hprefix.
      iModIntro.
      iDestruct (ghost_get_accepted_lb with "Hghost") as "#Hacc_lb".
      iSplitR "Heph".
      { iExists _; iFrame "∗#%". }
      iSplitR "Heph".
      {
        iApply (own_mono with "Hacc_lb").
        apply singleton_included. right.
        by apply mono_list_lb_mono.
      }
      iExists _.
      iFrame "∗#".
      done.
    }
    { (* case: not primary *)
      (* either increase the accepted ops to be opsfull, or conclude that the
         current accepted list already includes opsfull *)
      iMod ("HaccP" with "Hlc [Heph] Hstate") as "$"; last first.
      {
        (* PERF *)
        (* time done. *) (* takes 5 seconds*)
        (* time (iModIntro; done). *) (* takes 0.2 seconds, still a lot longer than below *)
        time (iModIntro; iApply True_intro; iAccu). }
      iIntros (opsold ? ?) "Hghost".
      iNamed "Hghost".

      destruct sealedold.
      { (* epoch can't be sealed because of own_ephemeral_proposal *)
        iNamed "Heph_sealed".
        iDestruct (own_valid_2 with "Heph Heph_sealed") as %Hbad.
        exfalso.
        rewrite singleton_op singleton_valid in Hbad.
        rewrite mono_list_auth_dfrac_op_valid_L in Hbad.
        destruct Hbad as [Hbad _].
        done.
      }

      iAssert (⌜prefix ops_durable_full opsfull0⌝)%I with "[-]" as %HdurablePrefix.
      { (* TODO: make this a separate lemma *)
        iNamed "Hghost".
        iDestruct (own_valid_2 with "Haccepted Hdurable_lb") as %H.
        iPureIntro.
        by rewrite singleton_op singleton_valid mono_list_both_valid_L in H.
      }

      (* opsfull0 is comparable to opsfull (by prop_lb). Maybe increase opsfull0
         to opsfull.
       *)
      iDestruct (ghost_get_proposal_facts with "Hghost") as "#[Hproposal_lb _]".
      iDestruct (own_valid_2 with "Hproposal_lb Hprop_lb") as %Hcomp.
      rewrite singleton_op singleton_valid in Hcomp.
      rewrite csum.Cinr_valid in Hcomp.
      apply mono_list_lb_op_valid_L in Hcomp.

      destruct Hcomp as [Hprefix|Hprefix].
      { (* case: opsfull0 ⪯ opsfull; do an update of accepted list.
           May or may not need to update ephemeral proposal.
         *)
        iMod (ghost_accept with "Hghost Hprop_lb Hprop_facts") as "Hghost".
        { done. }
        { by apply prefix_length. }
        iMod (ghost_primary_accept with "Hprop_facts Hprop_lb Hprim") as "Hprim".
        { by apply prefix_length. }

        iDestruct (own_valid_2 with "Heph_prop_lb Hprop_lb") as %Hephcases.
        rewrite singleton_op singleton_valid -csum.Cinr_op csum.Cinr_valid in Hephcases.
        rewrite mono_list_lb_op_valid_L in Hephcases.

        iDestruct (own_valid_2 with "Heph Heph_lb") as %Hephprefix.
        rewrite singleton_op singleton_valid in Hephprefix.
        rewrite mono_list_both_valid_L in Hephprefix.

        (* maybe update ephemeral proposal, maybe not. *)
        iAssert (
          |==> (∃ new_opsfull_ephemeral : list (GhostOpType * gname),
            ⌜get_rwops new_opsfull_ephemeral = get_rwops opsfull_ephemeral⌝ ∗ True ∗
            is_proposal_lb γ args.(RoApplyAsBackupArgs.epoch) new_opsfull_ephemeral ∗
            is_proposal_valid γ new_opsfull_ephemeral ∗
            own_ephemeral_proposal γeph args.(RoApplyAsBackupArgs.epoch) new_opsfull_ephemeral) ∗
            is_ephemeral_proposal_lb γeph args.(RoApplyAsBackupArgs.epoch) opsfull
          )%I with "[Heph]" as ">Heph".
        {
          destruct Hephcases as [Hephcase|Hephcase].
          {
            iMod (own_update with "Heph") as "Heph".
            { apply singleton_update. apply mono_list_update. apply Hephcase. }
            iDestruct (own_mono _ _ {[ _ := ◯ML _ ]} with "Heph") as "#Hnew_eph_lb".
            {
              apply singleton_mono.
              apply mono_list_included.
            }
            iModIntro.
            iFrame "#".
            iExists _.
            iFrame "∗#".
            iDestruct "Hprop_facts" as "(_ & _ & $)".
            iPureIntro.
            (* prove that the new opsfull_ephemeral (which is equal to opsfull) has the
               same rwops as the previous one. This makes use of the durable prefix. *)
            apply get_rwops_prefix in Hephcase.
            symmetry. apply list_prefix_eq.
            { done. }
            (* Given:
                ephemeral ⪯ newops,
                durable ⪯ cur,
                cur ⪯ newops,
                cur ⪯ ephemeral
                length newops ≤ length durable
               WTS:
                newops = ephemeral.
               Proof sketch:
                By squeezing.
                (durable ⪯ cur ⪯ newops) and (length newops ⪯ durable) → durable = newops = cur.
                Then, (ephemeral ⪯ newops = cur ⪯ ephemeral) → ephemeral = newops.
             *)
            assert (prefix (get_rwops ops_durable_full) (get_rwops opsfull)).
            {
              transitivity (get_rwops opsfull0).
              { apply get_rwops_prefix. done. }
              { apply get_rwops_prefix. done. }
            }
            apply list_prefix_eq in H; last first.
            { word. }
            apply get_rwops_prefix in HdurablePrefix, Hprefix, Hephprefix.
            apply prefix_length in HdurablePrefix, Hprefix, Hephcase, Hephprefix.
            word.
          }
          {
            iModIntro.
            iDestruct (own_mono _ _ {[ _ := ◯ML _ ]} with "Heph") as "#Htmp_eph_lb".
            {
              apply singleton_mono.
              apply mono_list_included.
            }
            iSplitL.
            {
              iExists _; iFrame "∗#".
              done.
            }
            iApply (own_mono with "Htmp_eph_lb").
            apply singleton_included.
            right.
            apply mono_list_lb_mono.
            done.
          }
        }
        iDestruct "Heph" as "[$ #Hnew_eph_lb]".
        iModIntro.
        iDestruct (ghost_get_accepted_lb with "Hghost") as "#Hacc_lb".
        iFrame "Hacc_lb".
        iExists _.
        iFrame.
        iFrame "#".
        subst.
        iPureIntro.
        (* Want to prove that opsfull.rws ⪯ opsfull0.rws
           Make use of durableNexftIndex.
         *)
        apply get_rwops_prefix in Hprefix.
        apply list_prefix_eq.
        { done. }
        apply prefix_length in Hprefix.
        rewrite Hσ_index.
        apply get_rwops_prefix, prefix_length in HdurablePrefix.
        word.
      }
      { (* case: opsfull ⪯ opsfull0; no need to do any update at all *)
        iDestruct (ghost_get_accepted_lb with "Hghost") as "#Hacc_lb".
        iModIntro.
        iSplitR "Heph".
        { iExists _; iFrame "∗#%". }
        iSplitR.
        {
          iApply (own_mono with "Hacc_lb").
          apply singleton_included. right. apply mono_list_lb_mono.
          done.
        }
        iExists opsfull_ephemeral.
        iFrame "∗#".
        done.
      }
    }
  }

  iMod "HH" as "HH".

Admitted. *)

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
  iMod (roapplybackup_step with "Hprop_lb Hprop_facts HisSm Hstate HghostEph") as "HH".
  { word. }
  { done. }

  wp_pures.
  wp_bind (struct.loadF _ _ _).
  wp_apply (wpc_nval_elim_wp with "HH").
  { done. }
  { done. }
  wp_loadField.
  wp_pures.
  iIntros "HH".
  iDestruct "HH" as (?) "(%Hnewops & Hstate & HghostEph & #Hacc_lb)".

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
