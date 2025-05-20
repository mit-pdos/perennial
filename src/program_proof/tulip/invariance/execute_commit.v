From Perennial.program_proof.tulip Require Import prelude.
From Perennial.program_proof.tulip.invariance Require Import execute_common.

Section execute_commit.
  Context `{!tulip_ghostG Σ}.

  Lemma replica_inv_execute_commit γ gid rid clog ilog ts pwrs :
    let clog' := clog ++ [CmdCommit ts pwrs] in
    is_txn_log_lb γ gid clog' -∗
    own_replica_clog_half γ gid rid clog -∗
    own_replica_ilog_half γ gid rid ilog -∗
    group_inv γ gid -∗
    replica_inv_weak γ gid rid ==∗
    own_replica_clog_half γ gid rid clog' ∗
    own_replica_ilog_half γ gid rid ilog ∗
    group_inv γ gid ∗
    replica_inv_weak γ gid rid.
  Proof.
    iIntros (clog') "#Hloglb Hclogprog Hilogprog Hgroup Hrp".
    iAssert (⌜not_stuck (apply_cmds clog')⌝)%I as %Hns.
    { do 2 iNamed "Hgroup".
      iDestruct (txn_log_prefix with "Hlog Hloglb") as %Hprefix.
      iPureIntro.
      eapply apply_cmds_not_stuck; [apply Hprefix | by rewrite Hrsm].
    }
    iAssert (is_txn_pwrs γ gid ts pwrs ∗ ⌜dom pwrs ⊆ keys_all⌝)%I as "[#Hpwrs %Hdompwrs]".
    { do 2 iNamed "Hgroup".
      rename Hcscincl into Hincl.
      iDestruct (txn_log_prefix with "Hlog Hloglb") as %Hprefix.
      assert (Hin : CmdCommit ts pwrs ∈ cpool).
      { rewrite /txn_cpool_subsume_log Forall_forall in Hincl.
        apply Hincl.
        subst clog'.
        eapply elem_of_prefix; last apply Hprefix.
        set_solver.
      }
      iDestruct (big_sepS_elem_of with "Hsafecp") as "Hsafec"; first apply Hin.
      iDestruct "Hsafec" as (wrs) "(_ & Hwrs & _ & %Hpwrs & %Hgid & %Hvwrs)".
      assert (Hdompwrs : dom pwrs ⊆ keys_all).
      { rewrite Hpwrs wrs_group_keys_group_dom. set_solver. }
      iFrame "Hwrs %".
    }
    do 2 iNamed "Hrp".
    (* Agreement on the consistent and inconsistent logs. *)
    iDestruct (replica_clog_agree with "Hclogprog Hclog") as %->.
    iDestruct (replica_ilog_agree with "Hilogprog Hilog") as %->.
    (* Update the consistent log. *)
    iMod (replica_clog_update clog' with "Hclogprog Hclog") as "[Hclogprog Hclog]".
    rewrite /not_stuck apply_cmds_snoc /= in Hns.
    set st := LocalState _ _ _ _ _ _ _ _ in Hrsm.
    (* Re-establish the RSM predicate. This will compute to the right form along
    the way in each branch. *)
    assert (Hrsm' : execute_cmds (merge_clog_ilog clog' ilog) = execute_commit st ts pwrs).
    { rewrite merge_clog_ilog_snoc_clog; last apply Hcloglen.
      by rewrite execute_cmds_snoc Hrsm.
    }
    iFrame "Hclogprog Hilogprog Hgroup".
    unshelve epose proof (execute_cmds_apply_cmds clog ilog cm histm _) as Happly.
    { by eauto 10. }
    rewrite /apply_commit Happly in Hns.
    subst st.
    rewrite /execute_commit in Hrsm'.
    assert (Hcloglen' : Forall (λ nc, (nc.1 <= length clog')%nat) ilog).
    { eapply Forall_impl; first apply Hcloglen.
      intros [n c] Hlen. simpl in Hlen.
      rewrite length_app /=.
      clear -Hlen. lia.
    }
    assert (Heqlast' : ge_lsn_last_ilog (length clog') ilog).
    { eapply ge_lsn_last_ilog_weaken; last apply Heqlast.
      rewrite length_app /=. lia.
    }
    destruct (cm !! ts) as [b |] eqn:Hcm.
    { (* Case: Txn [ts] already finalized. Contradiction for aborted; no-op for committed. *)
      destruct b; last done.
      by iFrame "∗ # %".
    }
    (* Case: Txn [ts] not finalized. *)
    (* Obtain facts about domain of the timestamp maps. *)
    pose proof (map_Forall2_dom_L _ _ _ Hlenkvd) as Hdomsptsm.
    symmetry in Hdomsptsm. rewrite Hdomkvdm in Hdomsptsm.
    pose proof (map_Forall2_dom_L _ _ _ Hsptsmlk) as Hdomptsm.
    symmetry in Hdomptsm. rewrite Hdomsptsm in Hdomptsm.
    destruct (cpm !! ts) as [pwrs' |] eqn:Hcpm.
    { (* Case: Txn [ts] prepared. *)      
      (* Extend history, set commit map to true, reset currently prepared map and release locks. *)
      iDestruct (big_sepM_delete _ _ ts with "Hsafep") as "[Hsafepwrs' Hsafep']".
      { apply Hcpm. }
      iDestruct (big_sepS_delete_affine _ _ ts with "Hlnrzs") as "Hlnrzs'".
      iDestruct (big_sepM_delete_affine _ _ ts with "Hsafebk") as "Hsafebk'".
      iClear "Hlnrzs Hsafebk".
      (* Agree on [pwrs] and [pwrs']. *)
      iDestruct (safe_txn_pwrs_impl_is_txn_pwrs with "Hsafepwrs'") as "Hpwrs'".
      iDestruct (txn_pwrs_agree with "Hpwrs Hpwrs'") as %->.
      iClear "Hsafep".
      set cm' := insert _ _ cm in Hrsm'.
      set histm' := multiwrite _ _ _ in Hrsm'.
      set cpm' := delete _ cpm in Hrsm'.
      set ptsm' := release _ ptsm in Hrsm'.
      iAssert (group_aborted_if_validated γ gid kvdm histm' ptsm')%I as "#Hgabt'".
      { iIntros (k t).
        destruct (decide (k ∈ dom pwrs)) as [Hin | Hnotin]; last first.
        { rewrite multiwrite_unmodified; last by apply not_elem_of_dom.
          by rewrite release_unmodified; last by apply not_elem_of_dom.
        }
        assert (is_Some (kvdm !! k)) as [vl Hvl].
        { rewrite -elem_of_dom Hdomkvdm. clear -Hin Hdompwrs. set_solver. }
        apply elem_of_dom in Hin as Hv.
        destruct Hv as [v Hv].
        pose proof (apply_cmds_dom _ _ _ Happly) as Hdomhistm.
        assert (is_Some (histm !! k)) as [h Hh].
        { rewrite -elem_of_dom Hdomhistm. clear -Hin Hdompwrs. set_solver. }
        rewrite (multiwrite_modified Hv Hh).
        rewrite release_modified; last first.
        { rewrite Hdomptsm. clear -Hin Hdompwrs. set_solver. }
        { apply Hin. }
        rewrite Hvl.
        destruct (vl !! t) as [b |] eqn:Hvlt; last done.
        destruct b; last done.
        clear Hns.
        destruct (decide ((length (last_extend ts h ++ [v]) <= t)%nat ∧ t ≠ 0%nat)) as [Ht |]; last done.
        (* case_decide as Ht; last done. *)
        destruct Ht as (Hgelen & Hnz).
        assert (is_Some (ptsm !! k)) as [pts Hpts].
        { rewrite -elem_of_dom Hdomptsm. clear -Hin Hdompwrs. set_solver. }
        iSpecialize ("Hgabt" $! k t).
        rewrite Hvl Hh Hpts Hvlt.
        destruct (decide ((length h <= t)%nat ∧ t ≠ pts)) as [| Ht]; first done.
        (* case_decide as Ht; first done. *)
        exfalso.
        apply Classical_Prop.not_and_or in Ht.
        destruct Ht as [Hltlen | Ht].
        { rewrite Nat.nle_gt in Hltlen.
          clear -Hgelen Hltlen.
          rewrite length_app /= in Hgelen.
          pose proof (last_extend_length_ge ts h) as Hlen.
          lia.
        }
        apply dec_stable in Ht. subst t.
        (* Prove that [k] must be locked by [ts] (i.e., [ts = pts]. *)
        specialize (Hpil _ _ _ Hcpm Hin).
        rewrite Hpil in Hpts. inv Hpts.
        pose proof (apply_cmds_hist_not_nil Happly) as Hnnil.
        specialize (Hnnil _ _ Hh). simpl in Hnnil.
        pose proof (last_extend_length_ge_n pts h Hnnil) as Hlen.
        rewrite length_app /= in Hgelen.
        clear -Hgelen Hlen. lia.
      }
      case_decide; last done.
      iFrame "∗ # %".
      iModIntro.
      iSplit.
      { rewrite dom_delete_L.
        iApply (big_sepS_subseteq with "Hrpvds").
        set_solver.
      }
      iSplit.
      { by rewrite dom_delete_L. }
      iPureIntro.
      split.
      { rewrite dom_insert_L dom_delete_L. clear -Hvtss.
        rewrite -union_assoc union_comm -union_assoc difference_union_L.
        set_solver.
      }
      split.
      { rewrite map_Forall2_forall.
        split; last by rewrite release_dom Hdomsptsm Hdomptsm.
        intros k spts pts Hspts Hpts Hnz.
        destruct (decide (k ∈ dom pwrs)) as [Hin | Hnotin]; last first.
        { rewrite release_unmodified in Hpts; last by apply not_elem_of_dom.
          apply (map_Forall2_lookup_Some _ _ _ _ _ _ Hspts Hpts Hsptsmlk Hnz).
        }
        rewrite release_modified in Hpts; last first.
        { rewrite Hdomptsm. clear -Hin Hdompwrs. set_solver. }
        { apply Hin. }
        inv Hpts.
      }
      split.
      { by apply prepared_impl_locked_inv_release. }
      { rewrite lookup_delete_None. by right. }
    }
    (* Case: Txn [ts] not prepared. Extend history and set commit map. *)
    set cm' := insert _ _ cm in Hrsm'.
    set histm' := multiwrite _ _ _ in Hrsm'.
    iAssert (group_aborted_if_validated γ gid kvdm histm' ptsm)%I as "#Hgabt'".
    { iIntros (k t).
      destruct (decide (k ∈ dom pwrs)) as [Hin | Hnotin]; last first.
      { by rewrite multiwrite_unmodified; last by apply not_elem_of_dom. }
      assert (is_Some (kvdm !! k)) as [vl Hvl].
      { rewrite -elem_of_dom Hdomkvdm. clear -Hin Hdompwrs. set_solver. }
      assert (is_Some (ptsm !! k)) as [pts Hpts].
      { rewrite -elem_of_dom Hdomptsm. clear -Hin Hdompwrs. set_solver. }
      rewrite Hvl Hpts.
      apply elem_of_dom in Hin as Hv.
      destruct Hv as [v Hv].
      pose proof (apply_cmds_dom _ _ _ Happly) as Hdomhistm.
      assert (is_Some (histm !! k)) as [h Hh].
      { rewrite -elem_of_dom Hdomhistm. clear -Hin Hdompwrs. set_solver. }
      rewrite (multiwrite_modified Hv Hh).
      destruct (vl !! t) as [b |] eqn:Hvlt; last done.
      destruct b; last done.
      clear Hns.
      destruct (decide ((length (last_extend ts h ++ [v]) <= t)%nat ∧ t ≠ pts)) as [Ht |]; last done.
      (* case_decide as Ht; last done. *)
      destruct Ht as [Hgelen Hnepts].
      iSpecialize ("Hgabt" $! k t).
      rewrite Hvl Hpts Hh Hvlt.
      destruct (decide ((length h <= t)%nat ∧ t ≠ pts)) as [| Ht]; first done.
      (* case_decide as Ht; first done. *)
      exfalso.
      apply Classical_Prop.not_and_or in Ht.
      destruct Ht as [Hltlen | ?]; last done.
      rewrite Nat.nle_gt in Hltlen.
      clear -Hgelen Hltlen.
      rewrite length_app /= in Hgelen.
      pose proof (last_extend_length_ge ts h) as Hlen.
      lia.
    }
    case_decide; last done.
    iFrame "∗ # %".
    iPureIntro.
    rewrite dom_insert_L.
    clear -Hvtss. set_solver.
  Qed.

End execute_commit.
