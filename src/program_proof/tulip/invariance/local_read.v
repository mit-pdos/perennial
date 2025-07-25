From Perennial.program_proof.tulip Require Import prelude.

Section local_read.
  Context `{!tulip_ghostG Σ}.

  Definition local_read_requirement st key rts hist :=
    match st with
    | LocalState cm histm cpm ptgsm sptsm ptsm bm ladm =>
        (∃ spts pts, sptsm !! key = Some spts ∧
                     ptsm !! key = Some pts ∧
                     histm !! key = Some hist ∧
                     (pts = O ∨ rts ≤ pts)%nat)
    | _ => False
    end.

  Lemma replica_inv_local_read {γ gid rid clog ilog st} key rts hist :
    valid_key key ->
    key_to_group key = gid ->
    execute_cmds (merge_clog_ilog clog ilog) = st ->
    local_read_requirement st key rts hist ->
    own_replica_clog_half γ gid rid clog -∗
    own_replica_ilog_half γ gid rid ilog -∗
    group_inv γ gid -∗
    replica_inv_weak γ gid rid ==∗
    own_replica_clog_half γ gid rid clog ∗
    own_replica_ilog_half γ gid rid (ilog ++ [(length clog, CmdRead rts key)]) ∗
    group_inv γ gid ∗
    replica_inv γ gid rid ∗
    read_promise γ gid rid key (pred (length hist)) rts ∗
    is_repl_hist_lb γ key hist.
  Proof.
    iIntros (Hvk Hgid Hst Hrequire) "Hclogprog Hilogprog Hgroup Hrp".
    do 2 iNamed "Hrp".
    (* Agreement on the consistent and inconsistent logs. *)
    iDestruct (replica_clog_agree with "Hclogprog Hclog") as %->.
    iDestruct (replica_ilog_agree with "Hilogprog Hilog") as %->.
    (* Update the inconsistent log. *)
    set ilog' := ilog ++ _.
    iMod (replica_ilog_update ilog' with "Hilogprog Hilog") as "[Hilogprog Hilog]".
    set st' := execute_read st rts key.
    assert (Hrsm' : execute_cmds (merge_clog_ilog clog ilog') = st').
    { rewrite merge_clog_ilog_snoc_ilog; last done.
      by rewrite execute_cmds_snoc Hst /=.
    }
    destruct st as [cmx histmx cpmx ptgsmx sptsmx ptsmx bmx laimx |]; last done.
    simpl in Hrequire.
    destruct Hrequire as (spts & pts & Hspts & Hpts & Hhist & Hlock).
    rewrite Hrsm in Hst. symmetry in Hst. inv Hst.
    (* [inv] eats the eq... *)
    set gid := key_to_group _.
    assert (is_Some (kvdm !! key)) as [vd Hvd].
    { pose proof (map_Forall2_dom_L _ _ _ Hlenkvd) as Hdomsptsm.
      by rewrite -elem_of_dom Hdomsptsm elem_of_dom.
    }
    pose proof (map_Forall2_lookup_Some _ _ _ _ _ _ Hvd Hspts Hlenkvd) as Hlenvd.
    simpl in Hlenvd.
    iDestruct (big_sepM_delete with "Hkvdm") as "[Hkvd Hkvdm]"; first apply Hvd.
    (* Obtain a lower-bound on the replicated history. *)
    iDestruct (group_inv_witness_repl_hist key hist with "Hcloglb Hgroup") as "#Hrepllb".
    { apply Hvk. }
    { done. }
    { unshelve epose proof (execute_cmds_apply_cmds clog ilog cm histm _) as Happly.
      { by eauto 10. }
      by rewrite /hist_from_log Happly.
    }
    (* Establish [eq_lsn_last_ilog (length clog) ilog'] with [ge_lsn_last_ilog ...]. *)
    assert (Heqlast' : eq_lsn_last_ilog (length clog) ilog').
    { by rewrite /eq_lsn_last_ilog last_snoc. }
    (* Re-establish [ilog_lsn_sorted ilog']. *)
    assert (Hisorted' : ilog_lsn_sorted ilog').
    { apply ilog_lsn_sorted_inv_snoc; [apply Heqlast | apply Hisorted]. }
    destruct (decide (pts = O)) as [Hz | Hnz]; last first.
    { (* Case: Key locked by txn [pts] where [rts ≤ pts]. No extension required. *)
      destruct Hlock as [? | Hle]; first done.
      pose proof (map_Forall2_lookup_Some _ _ _ _ _ _ Hspts Hpts Hsptsmlk Hnz) as Hsptslk.
      iAssert (read_promise γ gid rid key (pred (length hist)) rts)%I as "#Hpromise".
      { iDestruct (replica_key_validation_witness with "Hkvd") as "#Hkvdlb".
        iDestruct (replica_key_validation_lb_weaken (take rts vd) with "Hkvdlb") as "#Hlb".
        { apply prefix_take. }
        iFrame "Hlb".
        iSplit; last first.
        { iPureIntro.
          rewrite length_take.
          clear -Hlenvd Hsptslk Hle. lia.
        }
        iApply big_sepL_forall.
        iIntros (t b Hb [Htge ->]).
        assert (Hvdtrue : vd !! t = Some true).
        { eapply prefix_lookup_Some; first apply Hb.
          apply prefix_take.
        }
        iSpecialize ("Hgabt" $! key t).
        rewrite Hvd Hhist Hpts Hvdtrue.
        case_decide as Ht; first iFrame "Hgabt".
        exfalso.
        apply Classical_Prop.not_and_or in Ht.
        destruct Ht as [Htlt | Hnpt].
        { clear -Htlt Htge. lia. }
        apply dec_stable in Hnpt. subst t.
        apply lookup_lt_Some in Hb.
        rewrite length_take_le in Hb; last first.
        { clear -Hle Hlenvd Hsptslk. lia. }
        clear -Hb Hle. lia.
      }
      iDestruct (big_sepM_insert_2 with "Hkvd Hkvdm") as "Hkvdm".
      rewrite insert_delete_id; last apply Hvd.
      iFrame "∗ # %".
      iPureIntro.
      rewrite (lookup_alter_Some _ _ _ _ Hspts).
      replace (_ `max` _)%nat with spts by lia.
      split.
      { apply Forall_app_2; [apply Hcloglen | by rewrite Forall_singleton]. }
      by rewrite insert_id.
    }
    (* Case: Key not locked. *)
    destruct (decide (pred rts ≤ spts)%nat) as [Hle | Hgt].
    { (* Case: [rts ≤ spts]. No extension required. *)
      iAssert (read_promise γ gid rid key (pred (length hist)) rts)%I as "#Hpromise".
      { iDestruct (replica_key_validation_witness with "Hkvd") as "#Hkvdlb".
        iDestruct (replica_key_validation_lb_weaken (take rts vd) with "Hkvdlb") as "#Hlb".
        { apply prefix_take. }
        iFrame "Hlb".
        iSplit; last first.
        { iPureIntro.
          rewrite length_take.
          clear -Hlenvd Hle. lia.
        }
        iApply big_sepL_forall.
        iIntros (t b Hb [Htge ->]).
        assert (Hvdtrue : vd !! t = Some true).
        { eapply prefix_lookup_Some; first apply Hb.
          apply prefix_take.
        }
        iSpecialize ("Hgabt" $! key t).
        rewrite Hvd Hhist Hpts Hvdtrue.
        case_decide as Ht; first iFrame "Hgabt".
        exfalso.
        clear -Ht Htge Hz. lia.
      }
      iDestruct (big_sepM_insert_2 with "Hkvd Hkvdm") as "Hkvdm".
      rewrite insert_delete_id; last apply Hvd.
      iFrame "∗ # %".
      iPureIntro.
      rewrite (lookup_alter_Some _ _ _ _ Hspts).
      replace (_ `max` _)%nat with spts by lia.
      split.
      { apply Forall_app_2; [apply Hcloglen | by rewrite Forall_singleton]. }
      by rewrite insert_id.
    }
    (* Case: [spts < rts]. Extend the key validation list with [false] until
    [rts] and update the smallest ts to [rts]. *)
    rewrite Nat.nle_gt in Hgt.
    set vd' := extend rts false vd.
    iMod (replica_key_validation_update vd' with "Hkvd") as "Hkvd".
    { apply extend_prefix. }
    iAssert (read_promise γ gid rid key (pred (length hist)) rts)%I as "#Hpromise".
    { iDestruct (replica_key_validation_witness with "Hkvd") as "#Hkvdlb".
      iFrame "Hkvdlb".
      iSplit; last first.
      { iPureIntro. rewrite extend_length. clear -Hlenvd Hgt. lia. }
      iApply big_sepL_forall.
      iIntros (t b Hb [Htge ->]).
      destruct (decide (t < S spts)%nat) as [Hlt | Hge].
      { rewrite lookup_extend_l in Hb; last first.
        { clear -Hlenvd Hlt. lia. }
        iSpecialize ("Hgabt" $! key t).
        rewrite Hvd Hhist Hpts Hb.
        case_decide as Ht; first iFrame "Hgabt".
        exfalso.
        clear -Ht Htge Hz. lia.
      }
      exfalso.
      rewrite Nat.nlt_ge in Hge.
      apply lookup_lt_Some in Hb as Htlt.
      rewrite extend_length in Htlt.
      rewrite lookup_extend_r in Hb; first done.
      clear -Hlenvd Hgt Hge Htlt.
      lia.
    }
    iDestruct (big_sepM_insert_2 with "Hkvd Hkvdm") as "Hkvdm".
    rewrite insert_delete_eq.
    iFrame "∗ # %".
    iModIntro.
    iSplit.
    { iIntros (k t).
      destruct (decide (k = key)) as [-> | Hne]; last first.
      { by rewrite lookup_insert_ne. }
      rewrite lookup_insert_eq Hhist Hpts.
      destruct (decide (rts ≤ t)%nat) as [Hgerts | Hltrts].
      { rewrite lookup_ge_None_2; first done.
        rewrite extend_length.
        clear -Hlenvd Hgerts Hgt. lia.
      }
      rewrite Nat.nle_gt in Hltrts.
      destruct (decide (t < S spts)%nat) as [Hltspts | Hgespts]; last first.
      { rewrite Nat.nlt_ge in Hgespts.
        rewrite lookup_extend_r; first done.
        clear -Hlenvd Hltrts Hgespts.
        lia.
      }
      rewrite lookup_extend_l; last first.
      { clear -Hlenvd Hltspts. lia. }
      iSpecialize ("Hgabt" $! key t).
      by rewrite Hvd Hhist Hpts.
    }
    iPureIntro.
    rewrite (lookup_alter_Some _ _ _ _ Hspts).
    replace (_ `max` _)%nat with (pred rts) by lia.
    split.
    { apply Forall_app_2; [apply Hcloglen | by rewrite Forall_singleton]. }
    split.
    { rewrite dom_insert_L.
      apply elem_of_dom_2 in Hvd.
      clear -Hdomkvdm Hvd. set_solver.
    }
    split.
    { apply map_Forall2_insert_2; last apply Hlenkvd.
      rewrite extend_length.
      clear -Hlenvd Hgt. lia.
    }
    { rewrite map_Forall2_forall.
      split; last first.
      { rewrite dom_insert_L.
        pose proof (map_Forall2_dom_L _ _ _ Hsptsmlk) as Hdom.
        apply elem_of_dom_2 in Hspts.
        clear -Hdom Hspts. set_solver.
      }
      intros k sptsx ptsx Hsptsx Hptsx Hnz.
      destruct (decide (k = key)) as [-> | Hne]; last first.
      { rewrite lookup_insert_ne in Hsptsx; last done.
        rewrite map_Forall2_forall in Hsptsmlk.
        destruct Hsptsmlk as [Hsptsmlk _].
        by eapply Hsptsmlk.
      }
      exfalso.
      rewrite Hpts in Hptsx.
      clear -Hz Hnz Hptsx. inv Hptsx.
    }
  Qed.

End local_read.
