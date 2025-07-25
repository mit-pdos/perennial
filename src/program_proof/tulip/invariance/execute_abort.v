From Perennial.program_proof.tulip Require Import prelude.
From Perennial.program_proof.tulip.invariance Require Import execute_common.

Section execute_abort.
  Context `{!tulip_ghostG Σ}.

  Lemma replica_inv_execute_abort γ gid rid clog ilog ts :
    let clog' := clog ++ [CmdAbort ts] in
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
    iAssert (is_group_aborted γ gid ts)%I as "#Hgabtts".
    { do 2 iNamed "Hgroup".
      (* First, show that [ts] must have aborted after applying [clog']. *)
      destruct (apply_cmds clog') as [cmp histmp |] eqn:Happly; last done.
      assert (Habted : cmp !! ts = Some false).
      { rewrite apply_cmds_snoc /= /apply_abort in Happly.
        destruct (apply_cmds clog) as [cmpp histmpp |]; last done.
        destruct (cmpp !! ts) eqn:Hcmpp.
        { destruct b; first done.
          by inv Happly.
        }
        inv Happly.
        by rewrite lookup_insert_eq.
      }
      (* Next, show that [ts] must have aborted after applying the latest log. *)
      iDestruct (txn_log_prefix with "Hlog Hloglb") as %Hprefix.
      pose proof (apply_cmds_mono_cm Hprefix Hrsm Happly) as Hincl.
      pose proof (lookup_weaken _ _ _ _ Habted Hincl) as Habtedcm.
      iDestruct (group_commit_witness with "Hcm") as "#Hgabt".
      { apply Habtedcm. }
      iFrame "Hgabt".
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
    assert (Hrsm' : execute_cmds (merge_clog_ilog clog' ilog) = execute_abort st ts).
    { rewrite merge_clog_ilog_snoc_clog; last apply Hcloglen.
      by rewrite execute_cmds_snoc Hrsm.
    }
    iFrame "Hclogprog Hilogprog Hgroup".
    unshelve epose proof (execute_cmds_apply_cmds clog ilog cm histm _) as Happly.
    { by eauto 10. }
    rewrite /apply_abort Happly in Hns.
    subst st.
    rewrite /execute_abort in Hrsm'.
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
    { (* Case: Txn [ts] already finalized. Contradiction for committed; no-op for aborted. *)
      destruct b; first done.
      by iFrame "∗ # %".
    }
    (* Case: Txn [ts] not finalized. *)
    (* Obtain facts about domain of the timestamp maps. *)
    pose proof (map_Forall2_dom_L _ _ _ Hlenkvd) as Hdomsptsm.
    symmetry in Hdomsptsm. rewrite Hdomkvdm in Hdomsptsm.
    pose proof (map_Forall2_dom_L _ _ _ Hsptsmlk) as Hdomptsm.
    symmetry in Hdomptsm. rewrite Hdomsptsm in Hdomptsm.
    destruct (cpm !! ts) as [pwrs |] eqn:Hcpm.
    { (* Case: Txn [ts] prepared. *)
      (* Set commit map to false, reset currently prepared map and release locks. *)
      iDestruct (big_sepM_delete _ _ ts with "Hsafep") as "[Hpwrs Hsafep']".
      { apply Hcpm. }
      iDestruct (big_sepS_delete_affine _ _ ts with "Hlnrzs") as "Hlnrzs'".
      iDestruct (big_sepM_delete_affine _ _ ts with "Hsafebk") as "Hsafebk'".
      iClear "Hlnrzs Hsafebk".
      iAssert (⌜dom pwrs ⊆ keys_all⌝)%I as %Hdompwrs.
      { iDestruct "Hpwrs" as (wrs) "(_ & _ & %Hvwrs & _ & %Hpwrs)".
        iPureIntro.
        rewrite Hpwrs wrs_group_keys_group_dom. set_solver.
      }
      set cpm' := delete _ cpm in Hrsm'.
      set ptsm' := release _ ptsm in Hrsm'.
      iAssert (group_aborted_if_validated γ gid kvdm histm ptsm')%I as "#Hgabt'".
      { iIntros (k t).
        destruct (decide (k ∈ dom pwrs)) as [Hin | Hnotin]; last first.
        { by rewrite release_unmodified; last by apply not_elem_of_dom. }
        assert (is_Some (kvdm !! k)) as [vl Hvl].
        { rewrite -elem_of_dom Hdomkvdm. clear -Hin Hdompwrs. set_solver. }
        pose proof (apply_cmds_dom _ _ _ Happly) as Hdomhistm.
        assert (is_Some (histm !! k)) as [h Hh].
        { rewrite -elem_of_dom Hdomhistm. clear -Hin Hdompwrs. set_solver. }
        rewrite release_modified; last first.
        { rewrite Hdomptsm. clear -Hin Hdompwrs. set_solver. }
        { apply Hin. }
        rewrite Hvl Hh.
        destruct (vl !! t) as [b |] eqn:Hvlt; last done.
        destruct b; last done.
        case_decide as Ht; last done.
        destruct Ht as (Hgelen & Hnz).
        assert (is_Some (ptsm !! k)) as [pts Hpts].
        { rewrite -elem_of_dom Hdomptsm. clear -Hin Hdompwrs. set_solver. }
        iSpecialize ("Hgabt" $! k t).
        rewrite Hvl Hh Hpts Hvlt.
        case_decide as Ht; first done.
        apply Classical_Prop.not_and_or in Ht.
        destruct Ht as [Hltlen | Ht].
        { exfalso.
          rewrite Nat.nle_gt in Hltlen.
          clear -Hgelen Hltlen. lia.
        }
        apply dec_stable in Ht. subst t.
        (* Prove that [k] must be locked by [ts] (i.e., [ts = pts]. *)
        specialize (Hpil _ _ _ Hcpm Hin).
        rewrite Hpil in Hpts. inv Hpts.
        iFrame "Hgabtts".
      }
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
    (* Case: Txn [ts] not prepared. Set commit map to false. *)
    iFrame "∗ # %".
    iPureIntro.
    rewrite dom_insert_L.
    clear -Hvtss. set_solver.
  Qed.

End execute_abort.
