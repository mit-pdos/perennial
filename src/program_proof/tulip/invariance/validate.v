From Perennial.program_proof.tulip Require Import prelude.

Section validate.
  Context `{!tulip_ghostG Σ}.

  Definition validated_ptsm (ptsm : gmap dbkey nat) (pwrs : dbmap) :=
    map_Forall (λ _ pts, pts = O) (filter (λ kn, kn.1 ∈ dom pwrs) ptsm).

  Lemma validated_ptsm_lookup {ptsm pwrs k} :
    validated_ptsm ptsm pwrs ->
    k ∈ dom ptsm ->
    k ∈ dom pwrs ->
    ptsm !! k = Some O.
  Proof.
    intros Hvd Hinptsm Hinpwrs.
    apply elem_of_dom in Hinptsm as [pts Hpts].
    set f := λ kn : dbkey * nat, kn.1 ∈ dom pwrs.
    unshelve epose proof (map_lookup_filter_Some_2 f _ _ _ Hpts _) as Hpts'.
    { done. }
    specialize (Hvd _ _ Hpts'). simpl in Hvd.
    by subst pts.
  Qed.

  Definition validated_sptsm (sptsm : gmap dbkey nat) (ts : nat) (pwrs : dbmap) :=
    map_Forall (λ _ spts, (spts < ts)%nat) (filter (λ kn, kn.1 ∈ dom pwrs) sptsm).

  Lemma validated_sptsm_lookup {sptsm ts pwrs k spts} :
    validated_sptsm sptsm ts pwrs ->
    sptsm !! k = Some spts ->
    k ∈ dom pwrs ->
    (spts < ts)%nat.
  Proof.
    intros Hvd Hspts Hinpwrs.
    set f := λ kn : dbkey * nat, kn.1 ∈ dom pwrs.
    unshelve epose proof (map_lookup_filter_Some_2 f _ _ _ Hspts _) as Hspts'.
    { done. }
    by specialize (Hvd _ _ Hspts').
  Qed.

  Definition validate_requirement st ts pwrs :=
    match st with
    | LocalState cm histm cpm ptgsm sptsm ptsm bm ladm =>
        validated_ptsm ptsm pwrs ∧
        validated_sptsm sptsm ts pwrs ∧
        cpm !! ts = None
    | _ => False
    end.

  Lemma replica_inv_validate {γ gid rid clog ilog st} ts pwrs ptgs :
    execute_cmds (merge_clog_ilog clog ilog) = st ->
    validate_requirement st ts pwrs ->
    is_lnrz_tid γ ts -∗
    safe_txn_pwrs γ gid ts pwrs -∗
    safe_txn_ptgs γ ts ptgs -∗
    own_replica_clog_half γ gid rid clog -∗
    own_replica_ilog_half γ gid rid ilog -∗
    replica_inv_weak γ gid rid ==∗
    own_replica_clog_half γ gid rid clog ∗
    own_replica_ilog_half γ gid rid (ilog ++ [(length clog, CmdAcquire ts pwrs ptgs)]) ∗
    replica_inv γ gid rid ∗
    is_replica_validated_ts γ gid rid ts.
  Proof.
    iIntros (Hst Hrequire) "#Hlnrz #Hsafepwrs #Hsafeptgs Hclogprog Hilogprog Hrp".
    iDestruct (safe_txn_pwrs_dom_pwrs with "Hsafepwrs") as %Hdompwrs.
    do 2 iNamed "Hrp".
    (* Agreement on the consistent and inconsistent logs. *)
    iDestruct (replica_clog_agree with "Hclogprog Hclog") as %->.
    iDestruct (replica_ilog_agree with "Hilogprog Hilog") as %->.
    (* Update the inconsistent log. *)
    set ilog' := ilog ++ _.
    iMod (replica_ilog_update ilog' with "Hilogprog Hilog") as "[Hilogprog Hilog]".
    set st' := execute_acquire st ts pwrs ptgs.
    assert (Hrsm' : execute_cmds (merge_clog_ilog clog ilog') = st').
    { rewrite merge_clog_ilog_snoc_ilog; last done.
      by rewrite execute_cmds_snoc Hst /=.
    }
    destruct st as [cmx histmx cpmx ptgsmx sptsmx ptsmx bmx laimx |]; last done.
    simpl in Hrequire.
    destruct Hrequire as (Hvptsm & Hvsptsm & Hnp).
    rewrite Hrsm in Hst. symmetry in Hst. inv Hst.
    (* Insert [ts] into the set of validated timestamps [vtss]. *)
    iMod (replica_validated_ts_insert ts with "Hvtss") as "Hvtss".
    iDestruct (replica_validated_ts_witness ts with "Hvtss") as "#Htsvd".
    { set_solver. }
    (* Extend the validation list for each [k ∈ dom pwrs]. *)
    set kvdm' := validate ts pwrs kvdm.
    iMod (replica_key_validation_big_update kvdm' with "Hkvdm") as "Hkvdm".
    { rewrite map_Forall2_forall.
      split; last first.
      { by rewrite validate_dom. }
      intros k l l' Hl Hl'.
      destruct (pwrs !! k) as [v |] eqn:Hpwrsk;
        rewrite lookup_merge Hl Hpwrsk /= in Hl'; inv Hl'; last done.
      apply prefix_app_r, extend_prefix.
    }
    (* Obtain facts about domain of the timestamp maps. *)
    pose proof (map_Forall2_dom_L _ _ _ Hlenkvd) as Hdomsptsm.
    symmetry in Hdomsptsm. rewrite Hdomkvdm in Hdomsptsm.
    pose proof (map_Forall2_dom_L _ _ _ Hsptsmlk) as Hdomptsm.
    symmetry in Hdomptsm. rewrite Hdomsptsm in Hdomptsm.
    (* Obtain witnesses that for each key [k ∈ dom pwrs] has been validated. *)
    iAssert (validated_pwrs_of_txn γ gid rid ts)%I as "#Hvkeys".
    { iDestruct (safe_txn_pwrs_impl_is_txn_pwrs with "Hsafepwrs") as "Hpwrs".
      iFrame "Hpwrs".
      iDestruct (big_sepM_dom_subseteq_difference _ _ (dom pwrs) with "Hkvdm")
        as (m [Hdomm Hincl]) "[Hkvdm _]".
      { rewrite validate_dom Hdomkvdm. apply Hdompwrs. }
      iApply (big_sepM_sepS_impl with "Hkvdm"); first apply Hdomm.
      iIntros (k l Hl) "!> Hkvd".
      iDestruct (replica_key_validation_witness with "Hkvd") as "#Hlb".
      iFrame "Hlb".
      iPureIntro.
      pose proof (lookup_weaken _ _ _ _ Hl Hincl) as Hl'.
      apply elem_of_dom_2 in Hl.
      assert (is_Some (pwrs !! k)) as [v Hv].
      { by rewrite -elem_of_dom -Hdomm. }
      assert (is_Some (kvdm !! k)) as [vl Hvl].
      { rewrite -elem_of_dom Hdomkvdm. clear -Hl Hdomm Hdompwrs. set_solver. }
      rewrite lookup_merge Hv Hvl /= in Hl'.
      inv Hl'.
      assert (is_Some (sptsm !! k)) as [spts Hspts].
      { rewrite -elem_of_dom Hdomsptsm. clear -Hl Hdomm Hdompwrs. set_solver. }
      (* specialize (Hgespts _ _ Hspts). simpl in Hgespts. *)
      (* pose proof (lookup_weaken _ _ _ _ Hspts Hsptsmincl) as Hspts'. *)
      pose proof (map_Forall2_lookup_Some _ _ _ _ _ _ Hvl Hspts Hlenkvd) as Hlenvl.
      simpl in Hlenvl.
      unshelve epose proof (validated_sptsm_lookup Hvsptsm Hspts _) as Hle.
      { by apply elem_of_dom. }
      rewrite lookup_snoc_Some.
      right.
      split; last done.
      rewrite extend_length.
      clear -Hlenvl Hle. lia.
    }
    (* Re-establish [safe_txn_pwrs] over [<[ts := pwrs]> cpm]. *)
    iDestruct (big_sepM_insert_2 _ _ ts pwrs with "Hsafepwrs Hsafep") as "#Hsafep'".
    (* Re-establish [validated_pwrs_of_txn] over [{[ts]} ∪ vtss]. *)
    iDestruct (big_sepS_insert_2 ts with "Hvkeys Hvpwrs") as "#Hvpwrs'".
    iDestruct (big_sepS_insert_2 ts with "Hlnrz Hlnrzs") as "#Hlnrzs'".
    iDestruct (safe_txn_pwrs_ptgs_backup_txn with "Hsafepwrs Hsafeptgs") as "#Hbk".
    iDestruct (big_sepM_insert_2 _ _ ts ptgs with "Hbk Hsafebk") as "Hsafebk'".
    iClear "Hlnrzs Hsafebk".
    (* Establish [eq_lsn_last_ilog (length clog) ilog'] with [ge_lsn_last_ilog ...]. *)
    assert (Heqlast' : eq_lsn_last_ilog (length clog) ilog').
    { by rewrite /eq_lsn_last_ilog last_snoc. }
    (* Re-establish [ilog_lsn_sorted ilog']. *)
    assert (Hisorted' : ilog_lsn_sorted ilog').
    { apply ilog_lsn_sorted_inv_snoc; [apply Heqlast | apply Hisorted]. }
    iFrame "∗ # %".
    iModIntro.
    iSplit.
    { rewrite dom_insert_L.
      by iApply big_sepS_insert_2.
    }
    iSplit.
    { by rewrite dom_insert_L. }
    iSplit.
    { iIntros (k t).
      subst kvdm'.
      destruct (decide (k ∈ dom pwrs)) as [Hin | Hnotin]; last first.
      { rewrite validate_unmodified; last by apply not_elem_of_dom.
        by rewrite setts_unmodified; last by apply not_elem_of_dom.
      }
      assert (is_Some (kvdm !! k)) as [vl Hvl].
      { rewrite -elem_of_dom Hdomkvdm. clear -Hin Hdompwrs. set_solver. }
      rewrite (validate_modified Hin Hvl).
      unshelve erewrite (setts_modified Hin _).
      { rewrite Hdomptsm. clear -Hin Hdompwrs. set_solver. }
      destruct (histm !! k) as [hist |] eqn:Hhist; last done.
      destruct (decide (ts < t)%nat) as [Hgtts | Hlets].
      { (* Case: [ts < t]. *)
        rewrite lookup_ge_None_2; first done.
        rewrite length_app extend_length /=.
        assert (is_Some (sptsm !! k)) as [spts Hspts].
        { rewrite -elem_of_dom Hdomsptsm. clear -Hin Hdompwrs. set_solver. }
        pose proof (map_Forall2_lookup_Some _ _ _ _ _ _ Hvl Hspts Hlenkvd) as Hlenvl.
        simpl in Hlenvl.
        pose proof (validated_sptsm_lookup Hvsptsm Hspts Hin) as Hle.
        clear -Hlenvl Hle Hgtts. lia.
      }
      rewrite Nat.nlt_ge in Hlets.
      destruct (decide (t = ts)) as [-> | Hne].
      { (* Case: [ts = t]. *)
        destruct ((_ ++ [true]) !! ts); last done.
        destruct b; last done.
        case_decide as Hne; last done.
        by destruct Hne as [_ ?].
      }
      rewrite lookup_app_l; last first.
      { rewrite extend_length. clear -Hlets Hne. lia. }
      destruct (decide (length vl ≤ t)%nat) as [Hfalse | Hex].
      { (* Case: Extended part [length vl ≤ t < ts]. *)
        rewrite lookup_extend_r; first done.
        clear -Hlets Hne Hfalse. lia.
      }
      (* Case: The existing part [length vl < t]. *)
      rewrite Nat.nle_gt in Hex.
      rewrite lookup_extend_l; last apply Hex.
      iSpecialize ("Hgabt" $! k t).
      unshelve epose proof (validated_ptsm_lookup Hvptsm _ Hin) as Hz.
      { rewrite Hdomptsm. clear -Hin Hdompwrs. set_solver. }
      rewrite Hvl Hhist Hz.
      destruct (vl !! t) eqn:Hvlt; last done.
      destruct b; last done.
      case_decide as Htz; last first.
      { case_decide as Htts; last done.
        destruct Htts as [Htge Htts].
        apply Classical_Prop.not_and_or in Htz.
        destruct Htz as [? | Htz]; first done.
        apply dec_stable in Htz.
        subst t.
        unshelve epose proof (execute_cmds_apply_cmds clog ilog cm histm _) as Happly.
        { by eauto 10. }
        pose proof (apply_cmds_hist_not_nil Happly) as Hnnil.
        specialize (Hnnil _ _ Hhist). simpl in Hnnil.
        unshelve epose proof (nil_length_inv hist _) as ->; [lia | done].
      }
      by case_decide.
    }
    iDestruct (safe_txn_pwrs_impl_valid_ts with "Hsafepwrs") as %Hvts.
    iPureIntro.
    split.
    { apply Forall_app_2; [apply Hcloglen | by rewrite Forall_singleton]. }
    split.
    { rewrite dom_insert_L. clear -Hvtss. set_solver. }
    split.
    { by rewrite validate_dom. }
    split.
    { (* Re-establish constraint on validation lists and smallest preparable timestamps. *)
      rewrite map_Forall2_forall.
      split; last first.
      { by rewrite validate_dom Hdomkvdm setts_dom Hdomsptsm. }
      intros k vl' spts' Hvl' Hspts'.
      subst kvdm'.
      destruct (decide (k ∈ dom pwrs)) as [Hin | Hnotin]; last first.
      { rewrite validate_unmodified in Hvl'; last by apply not_elem_of_dom.
        rewrite setts_unmodified in Hspts'; last by apply not_elem_of_dom.
        by apply (map_Forall2_lookup_Some _ _ _ _ _ _ Hvl' Hspts' Hlenkvd).
      }
      assert (is_Some (kvdm !! k)) as [vl Hvl].
      { rewrite -elem_of_dom Hdomkvdm. clear -Hin Hdompwrs. set_solver. }
      rewrite (validate_modified Hin Hvl) in Hvl'.
      inv Hvl'.
      rewrite setts_modified in Hspts'; last first.
      { rewrite Hdomsptsm. clear -Hin Hdompwrs. set_solver. }
      { apply Hin. }
      assert (is_Some (sptsm !! k)) as [spts Hspts].
      { rewrite -elem_of_dom Hdomsptsm. clear -Hin Hdompwrs. set_solver. }
      inv Hspts'.
      pose proof (validated_sptsm_lookup Hvsptsm Hspts Hin) as Hle.
      pose proof (map_Forall2_lookup_Some _ _ _ _ _ _ Hvl Hspts Hlenkvd) as Hlen.
      simpl in Hlen.
      rewrite length_app extend_length /=.
      clear -Hle Hlen. lia.
    }
    split.
    { (* Re-establish constraint on prepare and smallest preparable timestamps. *)
      rewrite map_Forall2_forall.
      split; last first.
      { by rewrite 2!setts_dom Hdomsptsm Hdomptsm. }
      intros k spts pts Hspts' Hpts'.
      destruct (decide (k ∈ dom pwrs)) as [Hin | Hnotin]; last first.
      { rewrite setts_unmodified in Hspts'; last by apply not_elem_of_dom.
        rewrite setts_unmodified in Hpts'; last by apply not_elem_of_dom.
        by apply (map_Forall2_lookup_Some _ _ _ _ _ _ Hspts' Hpts' Hsptsmlk).
      }
      intros _.
      rewrite setts_modified in Hpts'; last first.
      { rewrite Hdomptsm. clear -Hin Hdompwrs. set_solver. }
      { apply Hin. }
      inv Hpts'.
      rewrite setts_modified in Hspts'; last first.
      { rewrite Hdomsptsm. clear -Hin Hdompwrs. set_solver. }
      { apply Hin. }
      by inv Hspts'.
    }
    split.
    { intros t w k Hw Hk.
      destruct (decide (t = ts)) as [-> | Hne]; last first.
      { rewrite lookup_insert_ne in Hw; last done.
        specialize (Hpil _ _ _ Hw Hk).
        destruct (decide (k ∈ dom pwrs)) as [Hin | Hnotin].
        { exfalso.
          set f := λ kn : dbkey * nat, kn.1 ∈ dom pwrs.
          unshelve epose proof (map_lookup_filter_Some_2 f _ _ _ Hpil _) as Hpts'.
          { apply Hin. }
          specialize (Hvptsm _ _ Hpts'). simpl in Hvptsm. subst t.
          clear -Hw Hcpmnz.
          inv Hw.
        }
        rewrite setts_unmodified; last by apply not_elem_of_dom.
        apply Hpil.
      }
      rewrite lookup_insert_eq in Hw.
      symmetry in Hw. inv Hw.
      rewrite setts_modified; [done | apply Hk |].
      rewrite Hdomptsm.
      clear -Hdompwrs Hk. set_solver.
    }
    { rewrite lookup_insert_ne; first done. clear -Hvts. rewrite /valid_ts in Hvts. lia. }
  Qed.

End validate.
