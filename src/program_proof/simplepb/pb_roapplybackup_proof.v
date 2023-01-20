From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.simplepb Require Import pb_ghost.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.program_proof.simplepb Require Import pb_definitions pb_marshal_proof pb_applybackup_proof.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.reconnectclient Require Import proof.

Section pb_roapplybackup_proof.

Context `{!heapGS Σ}.
Context {pb_record:PBRecord}.

Notation OpType := (pb_OpType pb_record).
Notation has_op_encoding := (pb_has_op_encoding pb_record).
Notation compute_reply := (pb_compute_reply pb_record).
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

  wp_loadField.
  wp_bind (If (_ > _) _ _).
  wp_apply (wp_wand with "[Hargs_index HnextIndex Hargs_epoch Hepoch]").
  {
    wp_loadField.
    wp_pures.
    wp_if_destruct.
    {
      wp_loadField.
      wp_loadField.
      wp_pures.
      iModIntro.
      (* FIXME: this is a very tedious proof *)
      instantiate (1:=(λ v, ("%Hisbool" ∷ ⌜v =
                        #(bool_decide (int.nat durableNextIndex < int.nat args.(RoApplyAsBackupArgs.nextIndex) ∧
                                      int.nat epoch = int.nat args.(RoApplyAsBackupArgs.epoch)))⌝) ∗ _)%I).
      simpl.
      iSplitR; last iNamedAccu.
      iPureIntro.
      destruct (bool_decide (epoch = args.(RoApplyAsBackupArgs.epoch))) eqn:X.
      {
        apply bool_decide_eq_true in X.
        rewrite X.
        rewrite bool_decide_true; last done.
        rewrite bool_decide_true; first done.
        split; last done.
        word.
      }
      {
        apply bool_decide_eq_false in X.
        rewrite bool_decide_false; last first.
        { naive_solver. }
        rewrite bool_decide_false; first done.
        rewrite not_and_r.
        right.
        destruct (decide (int.nat epoch = int.nat args.(RoApplyAsBackupArgs.epoch))).
        { exfalso. replace (epoch) with (args.(RoApplyAsBackupArgs.epoch)) in X by word.
          done. }
        naive_solver.
      }
    }
    {
      iFrame.
      iPureIntro.
      rewrite bool_decide_false; first done.
      rewrite not_and_r.
      left.
      word.
    }
  }
  iIntros (?).
  iNamed 1.
  wp_bind (If v _ #false).
  subst v.
  wp_apply (wp_wand with "[Hsealed]").
  {
    wp_pures.
    wp_if_destruct.
    {
      wp_pures.
      wp_loadField.
      wp_pures.
      instantiate (1:=(λ w, ("%Hisboolw" ∷ ⌜w = #(bool_decide (_))⌝ ∗ _)%I)).
      instantiate (3:=((int.nat durableNextIndex < int.nat args.(RoApplyAsBackupArgs.nextIndex))%Z
                       ∧ int.nat epoch = int.nat args.(RoApplyAsBackupArgs.epoch)
                       ∧ sealed = false)).
      simpl.
      iModIntro.
      iSplitR; last iNamedAccu.
      iPureIntro.
      destruct (bool_decide (sealed = false)) eqn:X.
      {
        apply bool_decide_eq_true in X.
        subst.
        rewrite bool_decide_true; last done.
        rewrite bool_decide_true; first done.
        destruct Heqb.
        split; done.
      }
      {
        apply bool_decide_eq_false in X.
        rewrite bool_decide_false; last first.
        { by destruct sealed. }
        rewrite bool_decide_false; first done.
        rewrite not_and_r.
        rewrite not_and_r.
        right. right.
        done.
      }
    }
    {
      wp_pures.
      iSplitR.
      { iPureIntro.
        rewrite bool_decide_false; first done.
        naive_solver. }
      by iFrame.
    }
  }

  iIntros (?).
  iNamed 1.
  wp_pures.
  rewrite Hisboolw.
  wp_if_destruct.
  { (* loop again *)
    wp_pures.
    wp_loadField.
    wp_apply (wp_condWait with "[-HΦ HΨ Hargs_epoch Hargs_index]").
    {
      iFrame "#".
      iFrame "Hlocked".
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
      iNext.
      (* time iFrame "∗#%". *)
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
      iNext.
      (* time iFrame "∗#%". *)
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
    { done. }
    { done. }
  }

  iAssert (_) with "HisSm" as "HisSm2".
  iEval (rewrite /is_StateMachine /tc_opaque) in "HisSm2".
  iNamed "HisSm2".

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
  wp_pures.
  wp_bind (struct.loadF _ _ _).
  wp_apply (wpc_nval_elim_wp with "HH").
  { done. }
  { done. }
  wp_loadField.
  wp_pures.
  iIntros "(Hstate & #Hacc_lb & HH)".
  iDestruct "HH" as (?) "(%Hrw_eq & %Hneweph & Hnew_prop_lb & #Hnew_prop_valid & Heph)".

  wp_apply (release_spec with "[-HΨ HΦ Hargs_epoch]").
  {
    iFrame "Hlocked HmuInv".
    iNext.
    repeat (iExists _).
    iFrame "Hsealed Heph ∗ Hdurable_lb #".
    rewrite Hrw_eq.
    iFrame.
    iSplitL "Hnew_prop_lb".
    {
      destruct isPrimary.
      { iModIntro. done. }
      { iDestruct "Hnew_prop_lb" as "#Hnew_prop_lb". iFrame "#". }
    }
    iFrame "%".
    destruct isPrimary.
    {
      subst.
      iFrame "#".
    }
    {
      by rewrite /is_possible_Primary /tc_opaque.
    }
  }
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iLeft in "HΨ".
  iApply "HΨ".
  iFrame "#".
  Unshelve.
  apply _.
Qed.

End pb_roapplybackup_proof.
