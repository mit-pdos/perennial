From Perennial.program_proof.tulip Require Import prelude.

Lemma ext_by_cmtd_inv_prepare repl cmtd kmod ts :
  kmod !! O = None ->
  kmod !! ts = None ->
  (length cmtd ≤ ts)%nat ->
  ext_by_cmtd repl cmtd kmod O ->
  ext_by_cmtd repl cmtd kmod ts.
Proof.
  intros Hz Hts Hlen Hdiff.
  rewrite /ext_by_cmtd Hz in Hdiff.
  destruct Hdiff as (rts & Hdiff & _).
  rewrite /ext_by_cmtd Hts.
  by eauto.
Qed.

Lemma prepared_impl_locked_inv_prepare stm ptsm ts pwrs :
  stm !! O = None ->
  dom pwrs ⊆ dom ptsm ->
  set_Forall (λ k, ptsm !! k = Some O) (dom pwrs) ->
  prepared_impl_locked stm ptsm ->
  prepared_impl_locked (<[ts:=StPrepared pwrs]> stm) (acquire ts pwrs ptsm).
Proof.
  intros Hnz Hincl Hfree Hpil tsx pwrsx key Hpwrsx Hkey.
  destruct (decide (tsx = ts)) as [-> | Hne]; last first.
  { rewrite lookup_insert_ne in Hpwrsx; last done.
    specialize (Hpil _ _ _ Hpwrsx Hkey).
    destruct (pwrs !! key) as [v |] eqn:Hpwrs.
    { exfalso.
      assert (Htsxnz : tsx ≠ O).
      { intros ->. by rewrite Hnz in Hpwrsx. }
      apply elem_of_dom_2 in Hpwrs.
      specialize (Hfree _ Hpwrs). simpl in Hfree.
      rewrite Hfree in Hpil.
      inv Hpil.
    }
    by rewrite setts_unmodified.
  }
  rewrite lookup_insert in Hpwrsx.
  inv Hpwrsx.
  apply setts_modified; [apply Hkey | set_solver].
Qed.

Lemma locked_impl_prepared_inv_prepare stm ptsm ts pwrs :
  dom pwrs ⊆ dom ptsm ->
  stm !! ts = None ->
  locked_impl_prepared stm ptsm ->
  locked_impl_prepared (<[ts:=StPrepared pwrs]> stm) (acquire ts pwrs ptsm).
Proof.
  intros Hincl Hnotin Hlip key tsx Htsx Hnz.
  destruct (decide (tsx = ts)) as [-> | Hne]; last first.
  { rewrite lookup_insert_ne; last done.
    apply Hlip; last done.
    destruct (pwrs !! key) as [v |] eqn:Hpwrs.
    { exfalso.
      apply elem_of_dom_2 in Hpwrs.
      rewrite setts_modified in Htsx; [inv Htsx | done | set_solver].
    }
    by rewrite -Htsx setts_unmodified.
  }
  exists pwrs.
  rewrite lookup_insert.
  split; first done.
  (* Prove that before this transition no keys are locked by [ts]. *)
  apply dec_stable.
  intros Hkey.
  apply not_elem_of_dom in Hkey.
  rewrite setts_unmodified in Htsx; last apply Hkey.
  specialize (Hlip _ _ Htsx Hnz).
  destruct Hlip as (pwrsx & Hpwrsx & _).
  by rewrite Hpwrsx in Hnotin.
Qed.

Section inv.
  Context `{!tulip_ghostG Σ}.

  Lemma key_inv_not_committed γ p gid ts pm key kmodc tsprep :
    gid = key_to_group key ->
    pm !! ts = None ->
    own_group_prepm γ gid pm -∗
    txnsys_inv γ p -∗
    key_inv_with_kmodc_no_tsprep γ key kmodc tsprep -∗
    ⌜kmodc !! ts = None⌝.
  Proof.
    iIntros (Hgid Hnone) "Hpm Htxnsys Hkey".
    do 2 iNamed "Htxnsys".
    destruct (resm !! ts) as [res |] eqn:Hlookup.
    { (* Case: Committed or aborted. *)
      iDestruct (big_sepM_lookup with "Hvr") as "Hres"; first apply Hlookup.
      destruct res.
      { (* Case: Committed. *)
        simpl.
        destruct (wrs !! key) as [v |] eqn:Hkey.
        { (* Case: [key] in the write set of [ts]; contradiction. *)
          rewrite /all_prepared.
          iDestruct "Hres" as "[_ Hpreps]".
          iDestruct (big_sepS_elem_of _ _ gid with "Hpreps") as "Hprep".
          { rewrite Hgid. by eapply elem_of_key_to_group_ptgroups, elem_of_dom_2. }
          iDestruct (group_prep_lookup with "Hpm Hprep") as %Hprep.
          congruence.
        }
        (* Case: [key] not in the write set of [ts]. *)
        do 2 iNamed "Hkey".
        iDestruct (cmtd_kmod_vslice_agree with "Hkmodcs Hkmodc") as %Hkmodc.
        { apply Hall. }
        iPureIntro.
        subst kmodc.
        by eapply vslice_resm_to_tmods_committed_absent.
      }
      { (* Case: Aborted. *)
        do 2 iNamed "Hkey".
        iDestruct (cmtd_kmod_vslice_agree with "Hkmodcs Hkmodc") as %Hkmodc.
        { apply Hall. }
        iPureIntro.
        subst kmodc.
        by eapply vslice_resm_to_tmods_aborted.
      }
    }
    (* Case: Not committed or aborted. *)
    do 2 iNamed "Hkey".
    iDestruct (cmtd_kmod_vslice_agree with "Hkmodcs Hkmodc") as %Hkmodc.
    { apply Hall. }
    iPureIntro.
    subst kmodc.
    by eapply vslice_resm_to_tmods_not_terminated.
  Qed.

  Lemma keys_inv_not_committed γ p gid ts pm tspreps :
    set_Forall (λ k, key_to_group k = gid) (dom tspreps) ->
    pm !! ts = None ->
    ([∗ map] key ↦ tsprep ∈ tspreps, key_inv_no_tsprep γ key tsprep) -∗
    own_group_prepm γ gid pm -∗
    txnsys_inv γ p -∗
    ([∗ map] key ↦ tsprep ∈ tspreps, key_inv_xcmted_no_tsprep γ key tsprep ts) ∗
    own_group_prepm γ gid pm ∗
    txnsys_inv γ p.
  Proof.
    iIntros (Hgid Hnone) "Hkeys Hst Htxn".
    iApply (big_sepM_impl_res with "Hkeys [Hst Htxn]").
    { iFrame. } (* why can't $ do the work? *)
    iIntros "!>" (k t Hkt) "Hkey [Hst Htxn]".
    apply elem_of_dom_2 in Hkt.
    specialize (Hgid _ Hkt). simpl in Hgid.
    iDestruct (key_inv_no_tsprep_unseal_kmodc with "Hkey") as (kmodc) "Hkey".
    iDestruct (key_inv_not_committed with "Hst Htxn Hkey") as %Hprep; first done.
    { apply Hnone. }
    iFrame "∗ %".
  Qed.

  Lemma key_inv_prepare {γ gid ts cm} pwrs k :
    ts ≠ O ->
    key_to_group k = gid ->
    k ∈ dom pwrs ->
    cm !! ts = None ->
    quorum_validated γ gid ts -∗
    is_txn_pwrs γ gid ts pwrs -∗
    key_inv_xcmted_no_tsprep γ k O ts -∗
    ([∗ set] rid ∈ rids_all, replica_inv_xfinalized γ gid rid {[ts]}) -∗
    own_group_commit_map γ gid cm -∗
    key_inv_xcmted_no_tsprep γ k ts ts ∗
    ([∗ set] rid ∈ rids_all, replica_inv_xfinalized γ gid rid {[ts]}) ∗
    own_group_commit_map γ gid cm.
  Proof.
    iIntros (Hnz Hgid Hk Hcm) "#Hqv #Hpwrs Hkey Hrps Hcm".
    do 3 iNamed "Hkey".
    destruct (decide (ts < pred (length cmtd))%nat) as [Hlt | Hge].
    { (* From [Hqv] and [Hqpa] we obtain a replica that currently grants the
         lock of [k] to [ts], but also has already validated or read [k] with a
         larger timestamp. *)
      iDestruct "Hqv" as (ridsq1) "[Hqv %Hq1]".
      iDestruct "Hqvfb" as (ridsq2) "[Hqvfb %Hq2]".
      pose proof (cquorums_overlapped _ _ _ Hq1 Hq2) as (rid & Hinq1 & Hinq2).
      pose proof (cquorum_elem_of _ _ _ Hinq1 Hq1) as Hinall.
      iDestruct (big_sepS_elem_of with "Hqv") as "Hrv"; first apply Hinq1.
      iDestruct (big_sepS_elem_of with "Hqvfb") as "Hrvfb"; first apply Hinq2.
      iDestruct (big_sepS_elem_of with "Hrps") as "Hrp"; first apply Hinall.
      iNamed "Hrp".
      iDestruct (replica_inv_xfinalized_validated_impl_prepared with "Hrv Hrp")
        as (pwrs') "%Hpreped".
      { apply Hxfinal. }
      { set_solver. }
      (* Prove [pwrs' = pwrs]. *)
      do 2 iNamed "Hrp".
      iDestruct (big_sepM_lookup with "Hsafep") as "Hsafepwrs'"; first apply Hpreped.
      iDestruct (safe_txn_pwrs_impl_is_txn_pwrs with "Hsafepwrs'") as "Hpwrs'".
      iDestruct (txn_pwrs_agree with "Hpwrs Hpwrs'") as %->.
      (* Prove [k] is locked by [ts]. *)
      specialize (Hpil _ _ _ Hpreped Hk).
      (* Prove the validation list for [k] has extended beyond [length cmtd]. *)
      iDestruct "Hrvfb" as (vdlb) "[Hvdlb %Hlen]".
      assert (is_Some (kvdm !! k)) as [vd Hvd].
      { by rewrite -elem_of_dom Hdomkvdm. }
      iDestruct (big_sepM_lookup with "Hkvdm") as "Hvd"; first apply Hvd.
      rewrite Hgid.
      iDestruct (replica_key_validation_prefix with "Hvdlb Hvd") as %Hprefix.
      exfalso.
      apply prefix_length in Hprefix.
      assert (is_Some (sptsm !! k)) as [spts Hspts].
      { pose proof (map_Forall2_dom_L _ _ _ Hsptsmlk) as Hdomsptsm.
        by rewrite -elem_of_dom Hdomsptsm elem_of_dom.
      }
      pose proof (map_Forall2_lookup_Some _ _ _ _ _ _ Hvd Hspts Hlenkvd) as Hlenvd.
      simpl in Hlenvd.
      pose proof (map_Forall2_lookup_Some _ _ _ _ _ _ Hspts Hpil Hsptsmlk Hnz) as Hub.
      clear -Hlt Hlen Hprefix Hlenvd Hub.
      lia.
    }
    rewrite Nat.nlt_ge in Hge.
    destruct (decide (ts = pred (length cmtd))) as [Heq | Hne].
    { (* From [Hqv] and [Hcori] we obtain a replica that currently grants the
         lock of [k] to [ts], but also has either invalidated (by txn [S ts]
         reading the key) at [ts] or received abort of [ts]. *)
      rewrite /committed_or_quorum_invalidated_key -Heq Hnc.
      iDestruct "Hqv" as (ridsq1) "[Hqv %Hq1]".
      iDestruct "Hcori" as "[Hcori | Habted]"; last first.
      { (* Prove the abort case is impossible. *)
        rewrite Hgid.
        iDestruct (group_commit_lookup with "Hcm Habted") as %Habted.
        by rewrite Habted in Hcm.
      }
      iDestruct "Hcori" as (ridsq2) "[Hcori %Hq2]".
      pose proof (cquorums_overlapped _ _ _ Hq1 Hq2) as (rid & Hinq1 & Hinq2).
      pose proof (cquorum_elem_of _ _ _ Hinq1 Hq1) as Hinall.
      iDestruct (big_sepS_elem_of with "Hqv") as "Hrv"; first apply Hinq1.
      iDestruct (big_sepS_elem_of with "Hcori") as "Hvdlb"; first apply Hinq2.
      iDestruct (big_sepS_elem_of with "Hrps") as "Hrp"; first apply Hinall.
      do 3 iNamed "Hrp".
      iDestruct (replica_validated_ts_elem_of with "Hrv Hvtss") as %Hinvtss.
      iDestruct (big_sepS_elem_of with "Hvpwrs") as (pwrs') "[Hpwrs' Hvdks]".
      { apply Hinvtss. }
      (* Prove [pwrs' = pwrs]. *)
      iDestruct (txn_pwrs_agree with "Hpwrs Hpwrs'") as %->.
      iDestruct (big_sepS_elem_of with "Hvdks") as "Hvdk"; first apply Hk.
      assert (is_Some (kvdm !! k)) as [vd Hvd].
      { by rewrite -elem_of_dom Hdomkvdm. }
      iDestruct (big_sepM_lookup with "Hkvdm") as "Hvd"; first apply Hvd.
      rewrite Hgid.
      iDestruct (replica_key_validation_lookup with "Hvdlb Hvd") as %Hneg.
      iDestruct (replica_key_validation_lookup with "Hvdk Hvd") as %Hpos.
      by rewrite Hneg in Hpos.
    }
    assert (Hle : (length cmtd ≤ ts)%nat) by lia.
    iFrame "∗ # %".
    iPureIntro.
    by apply ext_by_cmtd_inv_prepare.
  Qed.

  Lemma keys_inv_prepare γ gid ts cm pwrs :
    ts ≠ O ->
    cm !! ts = None ->
    quorum_validated γ gid ts -∗
    is_txn_pwrs γ gid ts pwrs -∗
    ([∗ set] key ∈ dom pwrs, key_inv_xcmted_no_tsprep γ key O ts) -∗
    ([∗ set] rid ∈ rids_all, replica_inv_xfinalized γ gid rid {[ts]}) -∗
    own_group_commit_map γ gid cm -∗
    ([∗ set] key ∈ dom pwrs, key_inv_xcmted_no_tsprep γ key ts ts) ∗
    ([∗ set] rid ∈ rids_all, replica_inv_xfinalized γ gid rid {[ts]}) ∗
    own_group_commit_map γ gid cm.
  Proof.
    iIntros (Hnz Hcm) "#Hqv #Hpwrs Hkeys Hrps Hcm".
    iAssert (⌜set_Forall (λ k, key_to_group k = gid) (dom pwrs)⌝)%I as %Hgroup.
    { iDestruct "Hpwrs" as (wrs) "[Hwrs %Hpwrs]".
      iPureIntro.
      rewrite /wrs_group in Hpwrs.
      intros k Hk.
      apply elem_of_dom in Hk as [v Hv].
      rewrite Hpwrs map_lookup_filter_Some in Hv.
      by destruct Hv as [_ Hgid].
    }
    iApply (big_sepS_impl_res with "Hkeys [Hrps Hcm]").
    { iFrame. }
    iIntros (k Hk) "!> Hkey [Hrps Hcm]".
    specialize (Hgroup _ Hk).
    by iApply (key_inv_prepare with "Hqv Hpwrs Hkey Hrps Hcm").
  Qed.

  Lemma replica_inv_not_finalized γ gid rid log cm histm tss ts :
    cm !! ts = None ->
    apply_cmds log = State cm histm ->
    replica_inv_xfinalized γ gid rid tss -∗
    own_txn_log_half γ gid log -∗
    replica_inv_xfinalized γ gid rid ({[ts]} ∪ tss) ∗
    own_txn_log_half γ gid log.
  Proof.
    iIntros (Hnone Happly) "Hrp Hlog".
    do 3 iNamed "Hrp".
    rename cm0 into cmrp.
    rename histm0 into histmrp.
    iDestruct (txn_log_prefix with "Hlog Hcloglb") as %Hprefix.
    unshelve epose proof (execute_cmds_apply_cmds clog ilog cmrp histmrp _) as Happly'.
    { by eauto. }
    pose proof (apply_cmds_mono_cm Hprefix Happly Happly') as Hincl.
    iFrame "Hlog ∗ # %".
    iPureIntro.
    apply set_Forall_union; last apply Hxfinal.
    rewrite set_Forall_singleton.
    by eapply lookup_weaken_None.
  Qed.

  Lemma replicas_inv_not_finalized γ gid rids log cm hists ts :
    cm !! ts = None ->
    apply_cmds log = State cm hists ->
    ([∗ set] rid ∈ rids, replica_inv γ gid rid) -∗
    own_txn_log_half γ gid log -∗
    ([∗ set] rid ∈ rids, replica_inv_xfinalized γ gid rid {[ts]}) ∗
    own_txn_log_half γ gid log.
  Proof.
    iIntros (Hxfinal Happly) "Hrps Hlog".
    iApply (big_sepS_impl_res with "Hrps Hlog").
    iIntros (rid Hrid) "!> Hrp Hlog".
    iDestruct (replica_inv_xfinalized_empty with "Hrp") as "Hrp".
    iDestruct (replica_inv_not_finalized with "Hrp Hlog") as "[Hrp Hlog]".
    { apply Hxfinal. }
    { apply Happly. }
    rewrite union_empty_r_L.
    iFrame.
  Qed.

  Lemma replica_inv_exclude_concurrent_prepare γ gid rid tss ts1 ts2 pwrs1 pwrs2 :
    ts1 ≠ ts2 ->
    ts1 ∈ tss ->
    ts2 ∈ tss ->
    dom pwrs1 ∩ dom pwrs2 ≠ ∅ ->
    is_replica_validated_ts γ gid rid ts1 -∗
    is_replica_validated_ts γ gid rid ts2 -∗
    is_txn_pwrs γ gid ts1 pwrs1 -∗
    is_txn_pwrs γ gid ts2 pwrs2 -∗
    replica_inv_xfinalized γ gid rid tss -∗
    False.
  Proof.
    iIntros (Hne Hin1 Hin2 Hoverlap) "Hts1 Hts2 Hpwrs1 Hpwrs2 Hrp".
    iNamed "Hrp".
    iDestruct (replica_inv_xfinalized_validated_impl_prepared with "Hts1 Hrp")
      as (pwrs1') "%Hpwrs1".
    { apply Hxfinal. }
    { apply Hin1. }
    iDestruct (replica_inv_xfinalized_validated_impl_prepared with "Hts2 Hrp")
      as (pwrs2') "%Hpwrs2".
    { apply Hxfinal. }
    { apply Hin2. }
    do 2 iNamed "Hrp".
    iAssert (⌜pwrs1' = pwrs1⌝)%I as %->.
    { iDestruct (big_sepM_lookup with "Hsafep") as "Hsafe"; first apply Hpwrs1.
      iDestruct (safe_txn_pwrs_impl_is_txn_pwrs with "Hsafe") as "Hpwrs1'".
      iApply (txn_pwrs_agree with "Hpwrs1 Hpwrs1'").
    }
    iAssert (⌜pwrs2' = pwrs2⌝)%I as %->.
    { iDestruct (big_sepM_lookup with "Hsafep") as "Hsafe"; first apply Hpwrs2.
      iDestruct (safe_txn_pwrs_impl_is_txn_pwrs with "Hsafe") as "Hpwrs2'".
      iApply (txn_pwrs_agree with "Hpwrs2 Hpwrs2'").
    }
    exfalso.
    apply set_choose_L in Hoverlap as [k Hk].
    apply elem_of_intersection in Hk as [Hinpwrs1 Hinpwrs2].
    pose proof (Hpil _ _ _ Hpwrs1 Hinpwrs1) as Hts1.
    pose proof (Hpil _ _ _ Hpwrs2 Hinpwrs2) as Hts2.
    rewrite Hts1 in Hts2.
    inv Hts2.
  Qed.

  Lemma repl_ts_setts_disjoint {γ} ts wrs tss :
    dom tss ## dom wrs ->
    ([∗ map] k ↦ t ∈ tss, own_repl_ts_half γ k t) -∗
    ([∗ map] k ↦ t ∈ acquire ts wrs tss, own_repl_ts_half γ k t).
  Proof.
    iIntros (Hdom) "Htpls".
    iApply (big_sepM_impl_dom_eq with "Htpls"); first apply setts_dom.
    iIntros "!>" (k ts1 ts2 Hts1 Hts2) "Hts".
    destruct (wrs !! k) as [v |] eqn:Hwrs.
    { apply elem_of_dom_2 in Hts1. apply elem_of_dom_2 in Hwrs. set_solver. }
    rewrite /acquire lookup_merge Hwrs Hts1 /= in Hts2.
    by inv Hts2.
  Qed.

  Lemma group_inv_prepare γ p gid ts pwrs :
    quorum_validated γ gid ts -∗
    quorum_prepared γ gid ts -∗
    safe_txn_pwrs γ gid ts pwrs -∗
    txnsys_inv γ p -∗
    ([∗ set] key ∈ keys_all, key_inv γ key) -∗
    ([∗ set] rid ∈ rids_all, replica_inv γ gid rid) -∗
    group_inv γ gid ==∗
    txnsys_inv γ p ∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    ([∗ set] rid ∈ rids_all, replica_inv γ gid rid) ∗
    group_inv γ gid ∗
    is_group_prepared γ gid ts.
  Proof.
    iIntros "#Hqv #Hqp #Hpwrs Htxnsys Hkeys Hrps Hgroup".
    do 2 iNamed "Hgroup".
    destruct (stm !! ts) as [st |] eqn:Hstm.
    { (* Case: Txn [ts] has already prepared, aborted, or committed. *)
      destruct st as [pwrs' | |].
      { (* Case: Prepared. Simply take the [is_group_prepared] in [Hsafestm]. *)
        iDestruct (big_sepM_lookup with "Hsafestm") as "#Hst"; first apply Hstm.
        iDestruct "Hst" as "[Hpreped _]".
        by iFrame "Htxnsys Hkeys Hrps ∗ # %".
      }
      { (* Case: Committed. Use stability to obtain [pm !! ts = true] and
           extract a witness. Note that another way to prove this case is to
           deduce preparedness from committedness. Having two ways to prove the
           same thing might suggest something is redudant? *)
        admit.
      }
      { (* Case: Aborted. Same as the committed case. Note that this case (i.e.,
           not prepared but aborted) could indeed happen if another participant
           group has aborted earlier. *)
        admit.
      }
    }
    (* Case: Txn [ts] has not prepared, aborted, or committed. *)
    assert (Hnone : pm !! ts = None).
    { apply not_elem_of_dom. apply not_elem_of_dom in Hstm. set_solver. }
    (* Take the required keys invariants. *)
    iDestruct "Hpwrs" as (wrs) "[Hwrs %Hpwrs]".
    destruct Hpwrs as (Hvts & Hvwrs & Hnempty & Hpwrs).
    iDestruct (big_sepS_subseteq_acc _ _ (dom pwrs) with "Hkeys") as "[Hkeys HkeysC]".
    { (* Prove [dom pwrs ⊆ keys_all] *)
      transitivity (dom wrs); last done.
      rewrite Hpwrs.
      apply dom_filter_subseteq.
    }
    (* Take the required prepare timestamps from the group invariant. *)
    iDestruct (big_sepM_dom_subseteq_difference _ _ (dom pwrs) with "Hlocks")
      as (tss [Hdom Hsubseteq]) "[Htss HlocksO]".
    { (* Prove [dom pwrs ⊆ dom (filter_group gid tssg)]. *)
      rewrite Hpwrs wrs_group_keys_group_dom filter_group_keys_group_dom Hdomptsm.
      set_solver.
    }
    (* Expose the prepare timestamps from keys invariant. *)
    iDestruct (keys_inv_extract_tsprep with "Hkeys") as (tssk) "(Hkeys & Htssk & %Hdom')".
    (* Agree on the prepare timestamps from the group and keys invariants. *)
    iDestruct (repl_ts_big_agree with "Htss Htssk") as %->; first by rewrite Hdom Hdom'.
    clear Hdom'.
    (* Update the prepare timestamps to [ts]. *)
    set tss' := gset_to_gmap ts (dom tss).
    iMod (repl_ts_big_update tss' with "Htss Htssk") as "[Htss Htssk]".
    { by rewrite dom_gset_to_gmap. }
    subst tss'.
    (* Prove txn [ts] has not committed on [tpls]. *)
    iDestruct (keys_inv_not_committed with "Hkeys Hpm Htxnsys") as "(Hkeys & Hpm & Htxn)".
    { intros k Hk.
      apply (key_to_group_filter_group _ _ tspreps).
      apply subseteq_dom in Hsubseteq.
      clear -Hsubseteq Hk. set_solver.
    }
    { apply Hnone. }
    (* Prove that [ts] has not finalized on any replica. *)
    assert (Hnotincm : cm !! ts = None).
    { by rewrite Hcm lookup_omap Hstm. }
    iDestruct (replicas_inv_not_finalized with "Hrps Hlog") as "[Hrps Hlog]".
    { apply Hnotincm. }
    { apply Hrsm. }
    (* Prove that keys modified by [ts] are not prepared by another txn. *)
    destruct (decide (map_Forall (λ _ t, t = O) tss)) as [Hallz | Hnz]; last first.
    { (* Case: Some key [k] is locked. Derive contradiction. *)
      apply map_not_Forall in Hnz as (k & pts & Hpts & Hnz); last apply _.
      (* Prove [tspreps !! k = Some pts]. *)
      unshelve epose proof (lookup_weaken _ tspreps _ _ Hpts _) as Hpts'.
      { trans (filter_group gid tspreps); [apply Hsubseteq | apply map_filter_subseteq]. }
      (* Obtain the write-set [pwrsx] of the conflicting txn [pts]. *)
      specialize (Hlip _ _ Hpts' Hnz).
      destruct Hlip as (pwrsx & Hpwrsx & Hinpwrsx).
      (* Prove [ts ≠ pts]. *)
      assert (Hne : ts ≠ pts).
      { intros ->. by rewrite Hpwrsx in Hstm. }
      (* From the fact that [pts] is prepared we obtain a quorum of nodes prepared for [pts]. *)
      iDestruct (big_sepM_lookup with "Hsafestm") as "Hsafe"; first apply Hpwrsx.
      iDestruct "Hsafe" as "[Hpreped Hsafe]".
      iDestruct (group_prep_lookup with "Hpm Hpreped") as %Hpreped.
      iDestruct (big_sepM_lookup with "Hsafepm") as "Hsafep"; first apply Hpreped.
      iDestruct "Hsafep" as "[_ Hqv']".
      (* Obtain two quorums from [Hqv] and [Hqv']. *)
      iDestruct "Hqv" as (ridsq1) "[Hvd1 %Hridsq1]".
      iDestruct "Hqv'" as (ridsq2) "[Hvd2 %Hridsq2]".
      (* Exhibit the replica that has prepared for both [ts] and [pts]. *)
      unshelve epose proof (quorums_overlapped rids_all ridsq1 ridsq2 _ _)
        as (rid & Hin1 & Hin2); [by left | by left |].
      iDestruct (big_sepS_elem_of with "Hvd1") as "Hvts"; first apply Hin1.
      iDestruct (big_sepS_elem_of with "Hvd2") as "Hvpts"; first apply Hin2.
      (* Obtain the replica invariant for [rid]. *)
      pose proof (cquorum_elem_of _ _ _ Hin1 Hridsq1) as Hin.
      iDestruct (big_sepS_elem_of with "Hrps") as "Hrp"; first apply Hin.
      (* Prove that [pts] also has not finalized on [rid]. *)
      assert (Hnotincmx : cm !! pts = None).
      { by rewrite Hcm lookup_omap Hpwrsx. }
      iDestruct (replica_inv_not_finalized with "Hrp Hlog") as "[Hrp Hlog]".
      { apply Hnotincmx. }
      { apply Hrsm. }
      iAssert (is_txn_pwrs γ gid ts pwrs)%I as "Hpwrs".
      { iFrame "Hwrs %". }
      iDestruct (safe_txn_pwrs_impl_is_txn_pwrs with "Hsafe") as "Hpwrsx".
      iDestruct (replica_inv_exclude_concurrent_prepare with "Hvts Hvpts Hpwrs Hpwrsx Hrp") as %[].
      { apply Hne. }
      { set_solver. }
      { set_solver. }
      { apply elem_of_dom_2 in Hpts.
        rewrite Hdom in Hpts.
        clear -Hpts Hinpwrsx. set_solver.
      }
    }
    (* Case: All keys are free. Encode this fact into the key invariants. *)
    iAssert ([∗ set] key ∈ dom tss, key_inv_xcmted_no_tsprep γ key O ts)%I
      with "[Hkeys]" as "Hkeys".
    { iApply (big_sepM_sepS_impl with "Hkeys"); first done.
      iIntros (k pts Hpts) "!> Hkey".
      specialize (Hallz _ _ Hpts). simpl in Hallz.
      by subst pts.
    }
    (* Re-establish keys invariant w.r.t. updated tuples. *)
    rewrite Hdom.
    iDestruct (keys_inv_prepare with "Hqv [] Hkeys Hrps Hcm") as "(Hkeys & Hrps & Hcm)".
    { rewrite /valid_ts in Hvts. lia. }
    { apply Hnotincm. }
    { iFrame "Hwrs %". }
    (* Put ownership of prepare timestamp back to keys invariant. *)
    iDestruct (keys_inv_merge_tsprep (dom pwrs) with "[Hkeys] Htssk") as "Hkeys".
    { by rewrite dom_gset_to_gmap. }
    { iApply (big_sepS_sepM_impl with "Hkeys"); first by rewrite dom_gset_to_gmap.
      iIntros (k t Hkt) "!> Hkey".
      apply lookup_gset_to_gmap_Some in Hkt as [_ ->].
      do 2 iNamed "Hkey".
      iFrame.
    }
    (* Merge the updated keys invariant back. *)
    iDestruct ("HkeysC" with "Hkeys") as "Hkeys".
    (* Merge ownership of tuples back to group invariants. *)
    iAssert ([∗ map] k ↦ x ∈ filter_group gid (acquire ts pwrs tspreps), own_repl_ts_half γ k x)%I
      with "[HlocksO Htss]" as "Hlocks".
    { iDestruct (repl_ts_setts_disjoint ts pwrs with "HlocksO") as "HlocksO".
      { clear -Hdom. set_solver. }
      rewrite /acquire setts_difference_distr.
      replace (gset_to_gmap _ _) with (acquire ts pwrs tss); last first.
      { apply map_eq.
        intros k.
        destruct (decide (k ∈ dom pwrs)) as [Hin | Hnotin].
        { rewrite setts_modified; [| done | by rewrite Hdom].
          symmetry.
          by rewrite lookup_gset_to_gmap_Some.
        }
        rewrite not_elem_of_dom in Hnotin.
        rewrite setts_unmodified; last apply Hnotin.
        replace (tss !! k) with (None : option nat); last first.
        { symmetry. by rewrite -not_elem_of_dom Hdom not_elem_of_dom. }
        symmetry.
        rewrite lookup_gset_to_gmap_None.
        by apply not_elem_of_dom.
      }
      iDestruct (big_sepM_subseteq_difference_2 with "Htss HlocksO") as "Hlocks".
      { by apply setts_mono. }
      by rewrite setts_filter_group_commute.
    }
    (* Insert [(ts, true)] into the prepare map and extract a witness. *)
    iMod (group_prep_insert ts true with "Hpm") as "[Hpm #Hpreped]"; first apply Hnone.
    (* Re-establish [safe_txnst] w.r.t. new status map. *)
    iAssert ([∗ map] ts ↦ st ∈ <[ts := StPrepared pwrs]> stm, safe_txnst γ gid ts st)%I
      as "Hsafestm'".
    { iApply big_sepM_insert_2; last done.
      by iFrame "Hwrs Hpreped".
    }
    iClear "Hsafestm".
    (* Re-establish [safe_prepare] w.r.t. new prepare map. *)
    iAssert ([∗ map] ts ↦ p ∈ <[ts := true]> pm, safe_prepare γ gid ts p)%I as "Hsafepm'".
    { iApply big_sepM_insert_2; last done.
      iFrame "Hqv Hqp".
    }
    iClear "Hsafepm".
    iFrame "∗ # %".
    iModIntro.
    iSplit.
    { iApply (big_sepS_mono with "Hrps").
      iIntros (rid Hrid) "Hrp".
      do 2 iNamed "Hrp".
      iFrame.
    }
    iPureIntro.
    assert (Hincl : dom pwrs ⊆ dom tspreps).
    { rewrite Hdomptsm.
      trans (dom wrs); last apply Hvwrs.
      rewrite Hpwrs. apply dom_filter_subseteq.
    }
    split.
    { rewrite 2!dom_insert_L. clear -Hdompm. set_solver. }
    split.
    { by rewrite setts_dom. }
    split.
    { rewrite omap_insert_None; last done.
      by rewrite -Hcm delete_notin.
    }
    split.
    { apply prepared_impl_locked_inv_prepare.
      { apply Htsnz. }
      { apply Hincl. }
      { intros k Hk.
        rewrite -Hdom elem_of_dom in Hk.
        destruct Hk as [t Ht].
        specialize (Hallz _ _ Ht). simpl in Hallz. subst t.
        eapply lookup_weaken; first apply Ht.
        trans (filter_group gid tspreps); first apply Hsubseteq.
        apply map_filter_subseteq.
      }
      { apply Hpil. }
    }
    split.
    { apply locked_impl_prepared_inv_prepare.
      { apply Hincl. }
      { apply Hstm. }
      { apply Hlip. }
    }
    { rewrite lookup_insert_ne; first apply Htsnz.
      rewrite /valid_ts in Hvts.
      lia.
    }
  Admitted.

End inv.
