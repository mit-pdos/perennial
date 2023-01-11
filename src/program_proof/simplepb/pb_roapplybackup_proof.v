From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.simplepb Require Import pb_ghost.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.program_proof.simplepb Require Import pb_definitions pb_marshal_proof.
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
Lemma wp_Clerk__ApplyAsBackup γ γsrv ck args_ptr (epoch nextIndex:u64) opsfull :
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
                ((own_ephemeral_proposal γeph args.(RoApplyAsBackupArgs.epoch) opsfull ∗
                is_ephemeral_proposal_lb γeph args.(RoApplyAsBackupArgs.epoch) opsfull) ∗
                ⌜prefix opsfull_ephemeral opsfull⌝ ∗
                ⌜isPrimary = false⌝
             ) )

           )%I) with "[Heph Hstate]" as "HH".
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
      iDestruct (ghost_propose_lb_valid with "Htok_used_witness Hprim Hprop_lb") as %Hvalid.
      iDestruct (own_valid_2 with "Heph Heph_lb") as %Hvalid2.
      exfalso.

      (* FIXME: move lemmas around *)
      (* apply get_rwops_prefix in Hvalid. *)
      apply get_rwops_prefix in Hvalid.
      apply prefix_length in Hvalid.
      rewrite Hσ_index in Hvalid.
      rewrite singleton_op singleton_valid in Hvalid2.
      apply mono_list_both_valid_L in Hvalid2.
      apply get_rwops_prefix in Hvalid2.
      apply prefix_length in Hvalid2.
      rewrite Hσ_nextIndex in Hvalid2.
      word.
    }
    { (* case: not primary *)
      iDestruct (own_valid_2 with "Heph_prop_lb Hprop_lb") as %Hcomp.
      rewrite singleton_op singleton_valid in Hcomp.
      rewrite csum.Cinr_valid in Hcomp.
      apply mono_list_lb_op_valid_L in Hcomp.
      destruct Hcomp as [Hprefix|Hprefix].
      2:{ (* case: opsfull_ephemeral ⪯ opsfull; no need to do any update at all *)
        exfalso.
        apply get_rwops_prefix, prefix_length in Hprefix.
        word.
      }
      {
        iMod (own_update with "Heph") as "Heph".
        {
          apply singleton_update.
          apply mono_list_update.
          exact Hprefix.
        }
        iDestruct (own_mono _ _ {[ _ := ◯ML _ ]} with "Heph") as "#Heph_lb".
        {
          apply singleton_mono.
          apply mono_list_included.
        }
        iModIntro.
        iApply wpc_nval_intro.
        iNext.
        iFrame "∗#".
        done.
      }
    }
  }

  iMod "HH" as "HH".
  wp_bind (struct.loadF _ _ _).
  wp_apply (wpc_nval_elim_wp with "HH").
  { done. }
  { done. }
  wp_loadField.
  wp_pures.
  iIntros "(Hstate & (Heph & #Heph_lb2) & %Heph_prefix & %HnotPrimary)".
  subst isPrimary.

  iMod (readonly_alloc_1 with "Hargs_op_sl") as "Hargs_op_sl".

  wp_apply ("HapplySpec" with "[$Hstate $Hargs_op_sl]").
  { (* prove protocol step *)
    iSplitL ""; first done.
    iIntros "Hghost".
    iNamed "Hghost".

    (* deal with implicitly accepting RO ops here *)
    rewrite Hre.
    iDestruct (ghost_accept_helper2 with "Hprop_lb Hghost") as "[Hghost %Hcomp]".
    epose proof (accept_helper _ _ _ _ Hcomp Hghost_op_σ) as H.
    eassert _ as H2; last apply H in H2.
    {
      rewrite Hσ_index.
      rewrite -Hre.
      rewrite Hσ_nextIndex.
      word.
    }
    destruct H2 as [HnewOp Hprefix].
    clear H.

    iMod (ghost_accept with "Hghost Hprop_lb Hprop_facts") as "Hghost".
    { done. }
    { by apply prefix_length. }
    iMod (ghost_primary_accept with "Hprop_facts Hprop_lb Hprim") as "Hprim".
    { by apply prefix_length. }

    iDestruct (ghost_get_accepted_lb with "Hghost") as "#Hacc_lb".
    iDestruct (ghost_get_epoch_lb with "Hghost") as "#Hepoch_lb2".
    instantiate (1:=(is_epoch_lb γsrv epoch ∗ is_accepted_lb γsrv epoch opsfull)%I).
    iModIntro.

    iSplitL.
    { iExists _; iFrame "Hghost".
      iFrame "Hprim".
      iFrame "#".
      done.
    }

    replace (epoch) with (args.(ApplyAsBackupArgs.epoch)) by word.
    iFrame "#".
  }
  iIntros (reply q waitFn) "(Hreply & Hstate & HwaitSpec)".
  wp_pures.
  wp_loadField.
  wp_storeField.
  wp_loadField.

  wp_loadField.
  wp_loadField.
  wp_apply (wp_MapGet with "HopAppliedConds_map").
  iIntros (cond ok) "[%Hlookup HopAppliedConds_map]".
  wp_pures.
  wp_bind (If _ _ _).
  wp_apply (wp_wand with "[HopAppliedConds_map HopAppliedConds HnextIndex]").
  {
    wp_if_destruct.
    { (* map lookup succeeded, signal the condvar *)
      apply map_get_true in Hlookup.
      iDestruct (big_sepM_lookup_acc with "HopAppliedConds_conds") as "[Hiscond _]".
      { done. }
      wp_apply (wp_condSignal with "Hiscond").
      wp_pures.
      wp_loadField.
      wp_loadField.
      wp_apply (wp_MapDelete with "HopAppliedConds_map").
      iIntros "HopAppliedConds_map".
      simpl.
      iAssert (∃ newOpAppliedConds,
                  is_map opAppliedConds_loc 1 newOpAppliedConds ∗
                  [∗ map] cond0 ∈ newOpAppliedConds, is_cond cond0 mu
              )%I with "[HopAppliedConds_map]" as "H".
      {
        iExists _; iFrame.
        unfold map_del.
        iDestruct (big_sepM_delete with "HopAppliedConds_conds") as "[_ $]".
        { done. }
      }
      (* FIXME: iNamedAccu and iAccu turn the strings into "^@^@^@^@^@..." *)
      instantiate (1:=(λ _, _)%I).
      instantiate (1:=
                  (
        "HopAppliedConds" ∷ s ↦[Server :: "opAppliedConds"] #opAppliedConds_loc ∗
        "HnextIndex" ∷ s ↦[Server :: "nextIndex"] #_ ∗
        "H" ∷ ∃ newOpAppliedConds, (is_map opAppliedConds_loc 1 newOpAppliedConds ∗
                ([∗ map] cond0 ∈ newOpAppliedConds, is_cond cond0 mu))
                )%I
      ).
      iAccu.
    }
    { (* FIXME: What are those weird ^@? *)
      simpl.
      iModIntro.
      iFrame.
      iExists _; iFrame "∗#".
    }
  }
  iIntros (?).
  iNamed 1.
  iDestruct "H" as (?) "[HopAppliedConds_map #HopAppliedConds_conds2]".
  wp_pures.

  wp_loadField.
  wp_apply (release_spec with "[-HΨ HΦ HwaitSpec Hargs_epoch]").
  {
    iFrame "Hlocked HmuInv".
    iNext.
    repeat (iExists _).
    replace ([op]) with ([(op, Q).1]) by done.
    replace (get_rwops opsfull_ephemeral ++ _) with (get_rwops opsfull); last first.
    {
      apply last_Some in Hghost_op_σ.
      destruct Hghost_op_σ as [opsprev Hghost_op].
      subst.
      rewrite get_rwops_app.
      simpl.
      apply get_rwops_prefix in Heph_prefix.
      rewrite get_rwops_app /= in Heph_prefix Hσ_index.
      eassert ((get_rwops [(_)]) = _) as ->.
      { unfold get_rwops. simpl. done. }
      f_equal.
      assert (length (get_rwops opsprev) = length (get_rwops opsfull_ephemeral)).
      {
        eassert ((get_rwops [(rw_op op, Q)]) = _) as H.
        { unfold get_rwops. simpl. done. }
        rewrite H app_length /= in Hσ_index.
        word.
      }
      (* length a = length b; a ⪯ b ++ [c] → a = b *)
      eassert (prefix (get_rwops opsprev) ((get_rwops opsprev) ++ get_rwops [(rw_op op, Q)])).
      { apply prefix_app_r. done. }
      pose proof (prefix_weak_total _ _ _ H0 Heph_prefix) as [Hcase|Hcase].
      { apply list_prefix_eq.
        { done. }
        { lia. }
      }
      { symmetry. apply list_prefix_eq.
        { done. }
        { lia. }
      }
    }
    iClear "Heph_lb2".
    time (iFrame "∗#"; iFrame "%").
    (* time (iFrame "∗"; iFrame "#"). *) (* PERF Not a big difference here because no % *)
    iSplitR.
    {
      iDestruct "Hprop_facts" as "(_ & _ & $)".
    }
    iPureIntro.
    word.
  }
  wp_pures.
  wp_apply "HwaitSpec".
  iIntros "#Hlb".
  wp_pures.

  (* possibly update durableNextIndex *)
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iClear "Hs_epoch_lb HopAppliedConds_conds HdurableNextIndex_is_cond HroOpsToPropose_is_cond".
  iClear "HcommittedNextRoIndex_is_cond Hdurable_lb Heph_prop_lb HprimaryOnly HisSm Heph_valid".
  (* FIXME: why doesn't Hdurable_lb get automatically get destructed into Hdurable_lb2? *)

  wp_pures.
  wp_bind  ((if: (if: _ then _ else _) then _ else _)%E).
  wp_apply (wp_wand with "[Hown Hargs_epoch]").
  {
    instantiate (1:= λ _, pb_definitions.own_Server s γ γsrv γeph own_StateMachine mu).
    iNamed "Hown".
    wp_bind (if: struct.loadF _ _ _ = _ then _ else _)%E.
    wp_loadField.
    wp_loadField.
    wp_if_destruct.
    {
      wp_loadField.
      wp_if_destruct.
      { (* case: increase durableNextIndex *)
        iDestruct "Hlb" as "[_ Hlb]".
        replace (epoch) with (args.(ApplyAsBackupArgs.epoch)) by word.
        wp_storeField.
        wp_loadField.
        wp_apply (wp_condBroadcast with "[]"); first iFrame "#".
        wp_pures.
        wp_loadField.
        wp_loadField.
        wp_bind ((if: #_ = #_ then _ else _)%E).
        wp_if_destruct.
        {
          wp_loadField.
          wp_loadField.
          wp_pures.
          wp_if_destruct.
          {
            wp_loadField.
            wp_apply (wp_condSignal with "[]"); first iFrame "#".
            repeat iExists _.
            (* time iFrame "Hlb ∗ #%". *) (* 11.484 secs *)
            time (iFrame "Hlb ∗ #"; iFrame "%"). (* 8.154 secs *)
            iPureIntro. word.
          }
          {
            repeat iExists _.
            iFrame "∗ Hlb #"; iFrame "%".
            iPureIntro.
            word.
          }
        }
        wp_pures.
        repeat iExists _.
        iFrame "∗ Hlb #"; iFrame "%".
        iPureIntro.
        word.
      }
      {
        repeat iExists _.
        (* time (iFrame "∗#%"). *) (* 11.501 secs *)
        time (iFrame "∗#"; iFrame "%"). (* 7.514 secs*)
        (* time (iFrame "∗"; iFrame "#"; iFrame "%"). *) (* secs *)
        iPureIntro.
        word.
      }
    }
    wp_pures.
    {
      iModIntro.
      repeat iExists _.
      iFrame "∗#"; iFrame "%".
    }
  }

  iIntros (?) "Hown".
  wp_pures.
  wp_loadField.
  wp_apply (release_spec with "[$HmuInv $Hlocked $Hown]").
  wp_pures.

  iLeft in "HΨ".
  iApply "HΦ".
  iApply "HΨ".
  replace (epoch) with (args.(ApplyAsBackupArgs.epoch)) by word.
  iDestruct "Hlb" as "(_ & $)".
  done.
Qed.

End pb_roapplybackup_proof.
