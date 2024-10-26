From Perennial.program_proof.tulip Require Import prelude.

Section local_read.
  Context `{!tulip_ghostG Σ}.

  Lemma replica_inv_local_read γ gid rid key rts spts pts hist :
    key ∈ keys_all ->
    (pts = O ∨ rts ≤ pts)%nat ->
    own_dura_hist_half γ rid key hist -∗
    own_replica_pts_half γ rid key pts -∗
    own_replica_spts_half γ rid key spts -∗
    replica_inv γ gid rid ==∗
    own_dura_hist_half γ rid key hist ∗
    own_replica_pts_half γ rid key pts ∗
    own_replica_spts_half γ rid key (spts `max` rts)%nat ∗
    replica_inv γ gid rid ∗
    read_promise γ gid rid key (pred (length hist)) rts ∗
    is_repl_hist_lb γ key hist.
  Proof.
    iIntros (Hkey Hlock) "Hhist Hpts Hspts Hrp".
    do 2 iNamed "Hrp".
    pose proof (apply_cmds_dom _ _ _ Hrsm) as Hdomhistm.
    pose proof (map_Forall2_dom_L _ _ _ Hlenkvd) as Hdomsptsm.
    symmetry in Hdomsptsm. rewrite Hdomkvdm in Hdomsptsm.
    pose proof (map_Forall2_dom_L _ _ _ Hsptsmlk) as Hdomptsm.
    symmetry in Hdomptsm. rewrite Hdomsptsm in Hdomptsm.
    assert (is_Some (histm !! key)) as [hist' Hhist]; first by rewrite -elem_of_dom Hdomhistm.
    assert (is_Some (kvdm !! key)) as [vd Hvd]; first by rewrite -elem_of_dom Hdomkvdm.
    assert (is_Some (sptsm !! key)) as [spts' Hspts]; first by rewrite -elem_of_dom Hdomsptsm.
    assert (is_Some (ptsm !! key)) as [pts' Hpts]; first by rewrite -elem_of_dom Hdomptsm.
    pose proof (map_Forall2_lookup_Some _ _ _ _ _ _ Hvd Hspts Hlenkvd) as Hlenvd.
    simpl in Hlenvd.
    iDestruct (big_sepM_lookup_acc with "Hhistm") as "[Hhistr HhistmC]"; first apply Hhist.
    iDestruct (big_sepM_delete with "Hkvdm") as "[Hkvd Hkvdm]"; first apply Hvd.
    iDestruct (big_sepM_delete with "Hsptsm") as "[Hsptsr Hsptsm]"; first apply Hspts.
    iDestruct (big_sepM_lookup_acc with "Hptsm") as "[Hptsr HptsmC]"; first apply Hpts.
    (* Agree on the history, prepare ts, and smallest preparable ts of [key]. *)
    iDestruct (dura_hist_agree with "Hhist Hhistr") as %->.
    iDestruct (replica_spts_agree with "Hspts Hsptsr") as %->.
    iDestruct (replica_pts_agree with "Hpts Hptsr") as %->.
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
      replace (_ `max` _)%nat with spts by lia.
      iDestruct ("HhistmC" with "Hhistr") as "Hhistm".
      iDestruct (big_sepM_insert_2 with "Hkvd Hkvdm") as "Hkvdm".
      rewrite insert_delete; last apply Hvd.
      iDestruct (big_sepM_insert_2 with "Hsptsr Hsptsm") as "Hsptsm".
      rewrite insert_delete; last apply Hspts.
      iDestruct ("HptsmC" with "Hptsr") as "Hptsm".
      (* Obtain a lower-bound on the replicated history. *)
      iDestruct (big_sepM_lookup with "Hreplhm") as "Hreplh"; first apply Hhist.
      by iFrame "∗ # %".
    }
    (* Case: Key not locked. *)
    destruct (decide (rts ≤ spts)%nat) as [Hle | Hgt].
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
      replace (_ `max` _)%nat with spts by lia.
      iDestruct ("HhistmC" with "Hhistr") as "Hhistm".
      iDestruct (big_sepM_insert_2 with "Hkvd Hkvdm") as "Hkvdm".
      rewrite insert_delete; last apply Hvd.
      iDestruct (big_sepM_insert_2 with "Hsptsr Hsptsm") as "Hsptsm".
      rewrite insert_delete; last apply Hspts.
      iDestruct ("HptsmC" with "Hptsr") as "Hptsm".
      (* Obtain a lower-bound on the replicated history. *)
      iDestruct (big_sepM_lookup with "Hreplhm") as "Hreplh"; first apply Hhist.
      by iFrame "∗ # %".
    }
    (* Case: [spts < rts]. Extend the key validation list with [false] until
    [rts] and update the smallest ts to [rts]. *)
    rewrite Nat.nle_gt in Hgt.
    set vd' := extend rts false vd.
    iMod (replica_key_validation_update vd' with "Hkvd") as "Hkvd".
    { apply extend_prefix. }
    iMod (replica_spts_update rts with "Hspts Hsptsr") as "[Hspts Hsptsr]".
    replace (_ `max` _)%nat with rts by lia.
    iAssert (read_promise γ gid rid key (pred (length hist)) rts)%I as "#Hpromise".
    { iDestruct (replica_key_validation_witness with "Hkvd") as "#Hkvdlb".
      iFrame "Hkvdlb".
      iSplit; last first.
      { iPureIntro. rewrite extend_length. clear -Hlenvd Hgt. lia. }
      iApply big_sepL_forall.
      iIntros (t b Hb [Htge ->]).
      destruct (decide (t < spts)%nat) as [Hlt | Hge].
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
      clear -Hlenvd Hgt Hge Htlt. lia.
    }
    iDestruct ("HhistmC" with "Hhistr") as "Hhistm".
    iDestruct (big_sepM_insert_2 with "Hkvd Hkvdm") as "Hkvdm".
    rewrite insert_delete_insert.
    iDestruct (big_sepM_insert_2 with "Hsptsr Hsptsm") as "Hsptsm".
    rewrite insert_delete_insert.
    iDestruct ("HptsmC" with "Hptsr") as "Hptsm".
    (* Obtain a lower-bound on the replicated history. *)
    iDestruct (big_sepM_lookup with "Hreplhm") as "Hreplh"; first apply Hhist.
    iFrame "∗ # %".
    iModIntro.
    iSplit.
    { iIntros (k t).
      destruct (decide (k = key)) as [-> | Hne]; last first.
      { by rewrite lookup_insert_ne. }
      rewrite lookup_insert Hhist Hpts.
      destruct (decide (rts ≤ t)%nat) as [Hgerts | Hltrts].
      { rewrite lookup_ge_None_2; first done.
        rewrite extend_length.
        clear -Hlenvd Hgerts Hgt. lia.
      }
      rewrite Nat.nle_gt in Hltrts.
      destruct (decide (t < spts)%nat) as [Hltspts | Hgespts]; last first.
      { rewrite Nat.nlt_ge in Hgespts.
        rewrite lookup_extend_r; first done.
        clear -Hlenvd Hltrts Hgespts. lia.
      }
      rewrite lookup_extend_l; last first.
      { clear -Hlenvd Hltspts. lia. }
      iSpecialize ("Hgabt" $! key t).
      by rewrite Hvd Hhist Hpts.
    }
    iPureIntro.
    split.
    { rewrite dom_insert_L.
      clear -Hkey Hdomkvdm. set_solver.
    }
    split.
    { apply map_Forall2_insert_2; last apply Hlenkvd.
      rewrite extend_length.
      clear -Hlenvd Hgt. lia.
    }
    { rewrite map_Forall2_forall.
      split; last first.
      { rewrite dom_insert_L. clear -Hkey Hdomsptsm Hdomptsm. set_solver. }
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
