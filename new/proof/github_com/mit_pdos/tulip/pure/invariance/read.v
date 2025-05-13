From Perennial.program_proof.tulip Require Import prelude.

Lemma ext_by_lnrz_inv_read ts cmtd lnrz kmodl :
  (ts ≤ length lnrz)%nat ->
  le_all ts (dom kmodl) ->
  ext_by_lnrz cmtd lnrz kmodl ->
  ext_by_lnrz (last_extend ts cmtd) lnrz kmodl.
Proof.
  intros Hlenl Hles Hext.
  destruct (decide (ts ≤ length cmtd)%nat) as [Hlenc | Hlenc].
  { (* Trivial if [cmtd] is not actually extended. *)
    by rewrite last_extend_id.
  }
  apply not_le in Hlenc.
  destruct Hext as (vlast & Hprefix & Hlast & Hlen & Hext).
  exists vlast.
  split.
  { (* Re-establish prefix. *)
    apply prefix_pointwise.
    intros i Hi.
    rewrite /last_extend Hlast /extend.
    destruct (decide (i < length cmtd)%nat) as [Hilt | Hige].
    { (* Case: before-extension [i < length cmtd]. *)
      rewrite lookup_app_l; last done.
      by apply prefix_lookup_lt.
    }
    (* Case: read-extension [length cmtd ≤ i]. *)
    rewrite Nat.nlt_ge in Hige.
    (* Obtain [i < ts]. *)
    rewrite last_extend_length_eq_n in Hi; [| set_solver | lia].
    assert (is_Some (lnrz !! i)) as [u Hu].
    { rewrite lookup_lt_is_Some. lia. }
    assert (Higeweak : (pred (length cmtd) ≤ i)%nat) by lia.
    specialize (Hext _ _ Higeweak Hu).
    rewrite lookup_app_r; last done.
    rewrite Hu lookup_replicate.
    split; last lia.
    rewrite -Hext.
    apply prev_dbval_lt_all.
    intros n Hn.
    (* Obtain [ts ≤ n]. *)
    specialize (Hles _ Hn). simpl in Hles.
    (* Prove [i < n] by [i < ts] and [ts ≤ n]. *)
    lia.
  }
  split.
  { (* Re-establish last. *)
    by rewrite last_last_extend.
  }
  split.
  { (* Re-establish len. *)
    intros n Hn.
    specialize (Hlen _ Hn). simpl in Hlen.
    specialize (Hles _ Hn). simpl in Hles.
    rewrite last_extend_length_eq_n; [| set_solver | lia].
    lia.
  }
  (* Re-establish ext. *)
  intros t u Ht Hu.
  rewrite last_extend_length_eq_n in Ht; [| set_solver | lia].
  apply Hext; [lia | done].
Qed.

Lemma ext_by_cmtd_inv_read {repl cmtd kmodc} rts pts :
  (pts ≠ O -> rts ≤ pts)%nat ->
  kmodc !! O = None ->
  repl ≠ [] ->
  ext_by_cmtd repl cmtd kmodc pts ->
  ext_by_cmtd repl (last_extend rts cmtd) kmodc pts.
Proof.
  rewrite /ext_by_cmtd.
  intros Hpts Hnone Hnnil Hext.
  destruct (decide (pts = O)) as [Hz | Hnz].
  { (* Case: [pts = O], i.e., key not prepared. *)
    rewrite Hz Hnone.
    rewrite Hz Hnone in Hext.
    destruct Hext as (rtsprev & Hcmtd & _).
    exists (rts `max` rtsprev)%nat.
    split; last done.
    by rewrite Hcmtd last_extend_twice.
  }
  specialize (Hpts Hnz).
  destruct (kmodc !! pts) as [v |].
  { (* Case: prepared and committed. *)
    destruct Hext as [-> Hlen].
    split; last done.
    rewrite last_extend_id; first done.
    rewrite length_app /= last_extend_length; last apply Hnnil.
    clear -Hpts. lia.
  }
  (* Case: prepared but not committed or aborted. *)
  destruct Hext as (rtsprev & Hext & Hlen).
  exists (rts `max` rtsprev)%nat.
  split; first by rewrite Hext last_extend_twice.
  intros _.
  specialize (Hlen Hnz).
  rewrite Hext last_extend_twice last_extend_length; last apply Hnnil.
  rewrite Hext last_extend_length in Hlen; last apply Hnnil.
  clear -Hlen Hpts. lia.
Qed.

Lemma cmtd_yield_from_kmodc_inv_read {cmtd kmodc} rts :
  cmtd ≠ [] ->
  gt_all (length cmtd) (dom kmodc) ->
  cmtd_yield_from_kmodc cmtd kmodc ->
  cmtd_yield_from_kmodc (last_extend rts cmtd) kmodc.
Proof.
  intros Hnnil Hgtall Hyield.
  destruct (decide (rts ≤ length cmtd)%nat) as [Hle | Hgt].
  { by rewrite last_extend_id. }
  rewrite Nat.nle_gt in Hgt.
  intros t Ht.
  destruct (decide (t < length cmtd)%nat) as [Hlt | Hge].
  { rewrite lookup_last_extend_l; last apply Hlt.
    by apply Hyield.
  }
  rewrite Nat.nlt_ge in Hge.
  rewrite last_extend_length_eq_n in Ht; [| done | lia].
  rewrite lookup_last_extend_r; [| lia | apply Ht].
  rewrite last_lookup Hyield; last first.
  { apply length_not_nil in Hnnil. clear -Hnnil. lia. }
  f_equal.
  symmetry.
  apply prev_dbval_ge; first lia.
  intros x Hx.
  specialize (Hgtall _ Hx). simpl in Hgtall.
  clear -Hgtall. lia.
Qed.

Lemma head_read_first_commit_compatible future ts tshd wrs keyhd :
  head_read future tshd keyhd ->
  first_commit_compatible future ts wrs ->
  keyhd ∈ dom wrs ->
  (tshd ≤ ts)%nat.
Proof.
  intros Hhr (lp & ls & (Happ & _ & Hhead) & Hcomp) Hnempty.
  destruct (decide (lp = [])) as [-> | Hnnil].
  { rewrite Happ /= /head_read Hhead in Hhr. inv Hhr. }
  assert (Hlp : ActRead tshd keyhd ∈ lp).
  { apply head_Some_elem_of.
    rewrite (head_prefix _ future); [done | apply Hnnil |].
    rewrite Happ.
    by apply prefix_app_r.
  }
  rewrite /compatible_all Forall_forall in Hcomp.
  specialize (Hcomp _ Hlp).
  destruct Hcomp; [lia | contradiction].
Qed.

Lemma conflict_free_inv_read {future tmodcs tid key} :
  head_read future tid key ->
  conflict_free future tmodcs ->
  conflict_free (tail future) tmodcs.
Proof.
  intros Hhead Hcf ts wrs Hwrs.
  specialize (Hcf _ _ Hwrs). simpl in Hcf.
  by unshelve eapply (first_commit_compatible_inv_tail_future _ _ _ _ _ Hhead).
Qed.

Lemma conflict_past_inv_read {past future tmodas tid key} :
  head_read future tid key ->
  conflict_past past future tmodas ->
  conflict_past (past ++ [ActRead tid key]) (tail future) tmodas.
Proof.
  intros Hhead Hcp ts form Hform.
  specialize (Hcp _ _ Hform). simpl in Hcp.
  rewrite /conflict_cases in Hcp.
  destruct form as [| | wrsx | wrsx]; simpl.
  - by apply no_commit_abort_inv_tail_future.
  - by unshelve eapply (first_abort_inv_tail_future _ _ _ _ Hhead).
  - by apply first_commit_incompatible_inv_snoc_past_tail_future.
  - by unshelve eapply (first_commit_compatible_inv_tail_future _ _ _ _ _ Hhead).
Qed.

Lemma cmtxn_in_past_inv_read {past resm} tid key :
  cmtxn_in_past past resm ->
  cmtxn_in_past (past ++ [ActRead tid key]) resm.
Proof.
  intros Hcmtxn ts wrs Hwrs.
  specialize (Hcmtxn _ _ Hwrs). simpl in Hcmtxn.
  set_solver.
Qed.

Section inv.
  Context `{!tulip_ghostG Σ}.

  Definition quorum_invalidated_key_or_group_aborted γ key ts : iProp Σ :=
    quorum_invalidated_key γ key ts ∨ is_group_aborted γ (key_to_group key) ts.

  Lemma key_inv_fast_read γ key ts vr vl :
    is_repl_hist_at γ key (pred ts) vr -∗
    is_lnrz_hist_at γ key (pred ts) vl -∗
    key_inv γ key -∗
    is_cmtd_hist_length_lb γ key ts ∗
    ⌜vl = vr⌝.
  Proof.
    iIntros "#Hvr #Hvl Hkey".
    do 2 iNamed "Hkey".
    iDestruct (lnrz_hist_lookup with "Hlnrz Hvl") as %Hvl.
    iDestruct (repl_hist_lookup with "Hrepl Hvr") as %Hvr.
    pose proof (ext_by_lnrz_impl_prefix_cmtd_lnrz _ _ _ Hdiffl) as Hprefixcl.
    pose proof (ext_by_cmtd_impl_prefix_repl_cmtd Hdiffc) as Hprefixrc.
    pose proof (prefix_lookup_Some _ _ _ _ Hvr Hprefixrc) as Hvrcmtd.
    apply lookup_lt_Some in Hvrcmtd as Hlencmtd.
    pose proof (prefix_lookup_lt _ _ _ Hlencmtd Hprefixcl) as Hvlvr.
    rewrite Hvrcmtd Hvl in Hvlvr.
    inv Hvlvr.
    iDestruct (cmtd_hist_witness with "Hcmtd") as "#Hcmtdlb".
    iFrame "Hcmtdlb".
    iPureIntro.
    split; last done.
    clear -Hlencmtd. lia.
  Qed.

  Lemma key_inv_quorum_read γ kmodc kmodl ts lts pts key vr vl :
    ts ≠ O ->
    (lts < ts)%nat ->
    (pts ≠ O -> ts ≤ pts)%nat ->
    outside_all lts (pred ts) (dom kmodc) ->
    le_all ts (dom kmodl) ->
    quorum_validation_fixed_before γ key ts -∗
    quorum_invalidated_key_or_group_aborted γ key (pred ts) -∗
    is_repl_hist_at γ key lts vr -∗
    is_lnrz_hist_at γ key (pred ts) vl -∗
    key_inv_with_kmodc_with_kmodl_with_pts γ key kmodc kmodl pts ==∗
    key_inv_with_kmodc_with_kmodl_with_pts γ key kmodc kmodl pts ∗
    is_cmtd_hist_length_lb γ key ts ∗
    ⌜vl = vr⌝.
  Proof.
    iIntros (Hnz Hltts Hpts Houtside Hleall) "#Hqvfbts #Hqikoa #Hvr #Hvl Hkey".
    do 2 iNamed "Hkey".
    iDestruct (lnrz_hist_lookup with "Hlnrz Hvl") as %Hvl.
    iDestruct (repl_hist_lookup with "Hrepl Hvr") as %Hvr.
    (* Re-establish [ext_by_lnrz]. *)
    assert (Hlenl : (ts ≤ length lnrz)%nat).
    { apply lookup_lt_Some in Hvl. lia. }
    pose proof (ext_by_lnrz_inv_read _ _ _ _ Hlenl Hleall Hdiffl) as Hdiffl'.
    (* Re-establish [ext_by_emtd]. *)
    unshelve epose proof (ext_by_cmtd_inv_read ts _ _ Hzrsv _ Hdiffc) as Hdiffc'.
    { apply Hpts. }
    { apply Hrnnil. }
    (* Extend [hist_cmtd_auth] to [tid]. Note that it's a no-op when [tid ≤ length cmtd]. *)
    set cmtd' := last_extend _ _ in Hdiffl' Hdiffc'.
    iMod (cmtd_hist_update cmtd' with "Hcmtd") as "Hcmtd".
    { apply last_extend_prefix. }
    pose proof (ext_by_lnrz_impl_cmtd_not_nil _ _ _ Hdiffl) as Hnnil.
    iAssert (is_cmtd_hist_length_lb γ key ts)%I as "#Hlb".
    { iDestruct (cmtd_hist_witness with "Hcmtd") as "#Hlb".
      iFrame "Hlb".
      iPureIntro.
      apply last_extend_length_ge_n, Hnnil.
    }
    (* Re-establish [cmtd_yield_from_kmodc]. *)
    pose proof (cmtd_yield_from_kmodc_inv_read ts Hnnil Hltlenc Hyield) as Hyield'.
    iAssert (⌜cmtd' !! pred ts = Some vr⌝)%I as %Hvr'.
    { pose proof (ext_by_cmtd_impl_prefix_repl_cmtd Hdiffc') as Hprefix.
      pose proof (prefix_lookup_Some _ _ _ _ Hvr Hprefix) as Hvr'.
      iPureIntro.
      unshelve epose proof (Hyield' (pred ts) _) as Hvatts.
      { rewrite last_extend_length; last apply Hnnil. lia. }
      unshelve epose proof (Hyield' lts _) as Hvatlts.
      { rewrite last_extend_length; last apply Hnnil. lia. }
      rewrite Hvatts -Hvr' Hvatlts.
      f_equal.
      symmetry.
      apply prev_dbval_outside.
      { clear -Hltts. lia. }
      { apply Houtside. }
    }
    (* Re-establish [gt_all (length cmtd') (dom kmodc)]. *)
    assert (gt_all (length cmtd') (dom kmodc)) as Hltlenc'.
    { eapply gt_all_weaken; [apply last_extend_length_ge | apply Hltlenc]. }
    (* Prove the linearized read is equal to the physical read. *)
    assert (Heq : vl = vr).
    { (* Obtain [prefix cmtd' lnrz]. *)
      destruct Hdiffl' as (_ & Hprefixcl & _).
      assert (Hlenc : (pred ts < length cmtd')%nat).
      { apply (Nat.lt_le_trans _ ts); last by apply last_extend_length_ge_n. lia. }
      pose proof (prefix_lookup_lt _ _ _ Hlenc Hprefixcl) as Hvl'.
      rewrite Hvl in Hvl'.
      rewrite Hvl' in Hvr'.
      by inv Hvr'.
    }
    iFrame "∗ # %".
    (* Prove [quorum_validation_fixed_before] and [committed_or_quorum_invalidated]. *)
    destruct (decide (ts ≤ length cmtd)%nat) as [Hle | Hgt].
    { subst cmtd'. rewrite last_extend_id; last apply Hle. by iFrame "Hqvfb Hcori". }
    rewrite Nat.nle_gt in Hgt.
    rewrite last_extend_length_eq_n; [| done | lia].
    iFrame "Hqvfbts".
    iModIntro.
    rewrite /committed_or_quorum_invalidated_key.
    destruct (kmodc !! (pred ts)); first done.
    iFrame "Hqikoa".
  Qed.

  Lemma txnsys_inv_read γ ts key vr vl future :
    ts ≠ O ->
    head_read future ts key ->
    fast_or_quorum_read γ key ts vr -∗
    is_lnrz_hist_at γ key (pred ts) vl -∗
    txnsys_inv_no_future γ future -∗
    group_inv γ (key_to_group key) -∗
    ([∗ set] rid ∈ rids_all, replica_inv γ (key_to_group key) rid) -∗
    key_inv γ key ==∗
    txnsys_inv_no_future γ (tail future) ∗
    group_inv γ (key_to_group key) ∗
    ([∗ set] rid ∈ rids_all, replica_inv γ (key_to_group key) rid) ∗
    key_inv γ key ∗
    ⌜vl = vr⌝.
  Proof.
    iIntros (Hnz Hhead) "#Hfoq #Hlnrzlb Htxnsys Hgroup Hrps Hkey".
    do 2 iNamed "Htxnsys".
    iDestruct "Hfoq" as "[Hfr | Hqr]".
    { (* Case: Fast-read. *)
      iDestruct (key_inv_fast_read with "Hfr Hlnrzlb Hkey") as "[#Hcmtd %Heq]".
      (* Re-establish [past_action_witness]. *)
      iAssert (past_action_witness γ (ActRead ts key))%I as "#Hpa"; first iFrame "Hcmtd".
      iCombine "Hpas Hpa" as "Hpas'".
      rewrite -big_sepL_snoc.
      (* Re-establish [conflict_free], [conflict_past], [cmtxn_in_past] w.r.t. read. *)
      pose proof (conflict_free_inv_read Hhead Hcf) as Hcf'.
      pose proof (conflict_past_inv_read Hhead Hcp) as Hcp'.
      pose proof (cmtxn_in_past_inv_read ts key Hcmtxn) as Hcmtxn'.
      by iFrame "∗ # %".
    }
    (* Case: Quorum-read. *)
    iDestruct (key_inv_expose_kmodc_kmodl_pts with "Hkey") as (kmodc kmodl pts) "Hkey".
    iAssert (⌜le_all ts (dom kmodl)⌝)%I as %Hleall.
    { do 2 iNamed "Hkey".
      iDestruct (big_sepS_elem_of _ _ key with "Hkmodls") as "Hkmodl'".
      { apply Hall. }
      iDestruct (lnrz_kmod_agree with "Hkmodl' Hkmodl") as %->.
      iPureIntro.
      intros tsx Htsx.
      apply elem_of_dom_vslice in Htsx as [wrs [Hwrs Hinwrs]].
      specialize (Hcf _ _ Hwrs). simpl in Hcf.
      eapply head_read_first_commit_compatible; [apply Hhead | apply Hcf | apply Hinwrs].
    }
    iAssert (⌜(pts ≠ O -> ts ≤ pts)%nat⌝)%I as %Hpts.
    { iIntros (Hptsnz).
      (* First, prove [pts] must have prepared but not finalized on group [key_to_group key]. *)
      do 2 iNamed "Hkey".
      do 2 iNamed "Hgroup".
      iAssert (⌜∃ pwrs, stm !! pts = Some (StPrepared pwrs) ∧ key ∈ dom pwrs⌝)%I
        as %(pwrs & Hpwrs & Hinpwrs).
      { assert (is_Some (tspreps !! key)) as [p Hp].
        { by rewrite -elem_of_dom Hdomptsm. }
        pose proof (lookup_filter_group_key_to_group _ _ _ Hp) as Hpin.
        iDestruct (big_sepM_lookup with "Hlocks") as "Hlock"; first apply Hpin.
        iDestruct (repl_ts_agree with "Htsprep Hlock") as %->.
        by specialize (Hlip _ _ Hp Hptsnz).
      }
      iDestruct (big_sepM_lookup with "Hsafestm") as "Hst"; first apply Hpwrs.
      (* Obtain [is_group_prepared] and [is_txn_pwrs] for [pts]. *)
      iDestruct "Hst" as "[Hst Hsafepwrs]".
      iDestruct (safe_txn_pwrs_impl_is_txn_pwrs with "Hsafepwrs") as "Hpwrs".
      (* Obtain [pm !! pts = Some true] and [cm !! pts = None]. *)
      iDestruct (group_prep_lookup with "Hpm Hst") as %Hpreped.
      destruct (cm !! pts) as [c |] eqn:Hxfinal.
      { by rewrite Hcm lookup_omap Hpwrs in Hxfinal. }
      (* Next, obtain a replica that has read [key] with [ts] and also validated [pts]. *)
      iNamed "Hqr".
      iDestruct (big_sepM_lookup with "Hsafepm") as "Hsafep"; first apply Hpreped.
      iDestruct "Hsafep" as "[_ Hqv]".
      iDestruct "Hqv" as (ridsqv) "[Hvds %Hridsqv]".
      iDestruct (replicas_inv_validated_keys_of_txn with "Hvds [Hrps]") as "#Hvdks".
      { iApply (big_sepS_subseteq with "Hrps").
        by destruct Hridsqv as [? _].
      }
      destruct (cquorums_overlapped _ _ _ Hqrm Hridsqv) as (rid & Hinq & Hinqv).
      iDestruct (big_sepS_elem_of with "Hioa") as "Hread"; first apply Hinq.
      iDestruct (big_sepS_elem_of with "Hvdks") as "Hvdk"; first apply Hinqv.
      destruct (decide (pts < ts)%nat) as [Hptslt |?]; last first.
      { iPureIntro. lia. }
      iNamed "Hread".
      iDestruct "Hvdk" as (pwrs') "[Hpwrs' Hvdk]".
      iDestruct (txn_pwrs_agree with "Hpwrs Hpwrs'") as %->.
      iDestruct (big_sepS_elem_of with "Hvdk") as "Hvd"; first apply Hinpwrs.
      iDestruct (replica_key_validation_lb_lookup with "Hvd Hvdl") as %Hvd.
      { clear -Hptslt Hlenvdl. lia. }
      (* Obtain [lts < pts]. *)
      iAssert (⌜(lts < pts)%nat⌝)%I as %Hptsgt.
      { iDestruct "Hv" as (repllb) "[Hrepllb %Hlen]".
        apply lookup_lt_Some in Hlen.
        iDestruct (repl_hist_prefix with "Hrepl Hrepllb") as %Hprefix.
        iPureIntro.
        apply prefix_length in Hprefix.
        pose proof (ext_by_cmtd_length_repl _ _ _ _ Hptsnz Hdiffc) as Hgtlen.
        clear -Hlen Hprefix Hgtlen. lia.
      }
      iDestruct (big_sepL_lookup with "Habtifp") as "Habtg"; first apply Hvd.
      iSpecialize ("Habtg" with "[]").
      { iPureIntro.
        split; last done.
        clear -Hptslt Hptsgt. lia.
      }
      (* Derive contradiction from [Habtg] which says this group has aborted [pts]. *)
      iDestruct (group_commit_lookup with "Hcm Habtg") as %Habtg.
      by rewrite Habtg in Hxfinal.
    }
    iAssert (quorum_validation_fixed_before γ key ts)%I as "#Hqvfbts".
    { (* Prove [quorum_validation_fixed_before]. *)
      iNamed "Hqr".
      iExists (ridsq).
      iSplit; last done.
      iApply (big_sepS_mono with "Hioa").
      iIntros (rid Hrid) "Hioa".
      iNamed "Hioa".
      iFrame "Hvdl".
      iPureIntro.
      lia.
    }
    iAssert (quorum_invalidated_key_or_group_aborted γ key (pred ts))%I as "#Hqikoa".
    { iNamed "Hqr".
      iDestruct (big_sepS_exists_sepM with "Hioa") as (ioam) "[%Hdomioam Hioam]".
      destruct (decide (map_Forall (λ _ l, l !! (pred ts) = Some false) ioam))
        as [Hallfalse | Hsometrue]; last first.
      { iRight.
        apply map_not_Forall in Hsometrue as (rid & vdl & Hvdl & Htrue); last apply _.
        iDestruct (big_sepM_lookup with "Hioam") as "Hioar"; first apply Hvdl.
        iNamed "Hioar".
        assert (is_Some (vdl !! (pred ts))) as [vd Hvd].
        { rewrite lookup_lt_is_Some. clear -Hnz Hlenvdl. lia. }
        destruct vd; last done.
        iDestruct (big_sepL_lookup with "Habtifp") as "#Habtgroup"; first apply Hvd.
        iSpecialize ("Habtgroup" with "[]").
        { iPureIntro. split; last done. clear -Hltts. lia. }
        done.
      }
      iLeft.
      iExists ridsq.
      iSplit; last done.
      iApply big_sepS_forall.
      iIntros (rid Hrid).
      assert (is_Some (ioam !! rid)) as [vdl Hvdl].
      { by rewrite -elem_of_dom Hdomioam. }
      iDestruct (big_sepM_lookup with "Hioam") as "Hrioa"; first apply Hvdl.
      iNamed "Hrioa".
      iFrame "Hvdl".
      assert (is_Some (vdl !! (pred ts))) as [vd Hvd].
      { rewrite lookup_lt_is_Some. clear -Hnz Hlenvdl. lia. }
      destruct vd; last done.
      specialize (Hallfalse _ _ Hvdl).
      by rewrite Hvd in Hallfalse.
    }
    iAssert (∃ lts, is_repl_hist_at γ key lts vr ∗
                    ⌜(lts < ts)%nat⌝ ∗
                    ⌜outside_all lts (pred ts) (dom kmodc)⌝)%I
      as (lts) "(#Hrepllb & %Hltts & %Houtside)".
    { iNamed "Hqr".
      iFrame "Hv".
      iSplit.
      { iPureIntro. clear -Hltts. lia. }
      do 2 iNamed "Hkey".
      iIntros (t Ht).
      apply elem_of_dom in Ht as [v Hv].
      destruct (decide (lts < t < ts)%nat) as [Ht | Ht]; last first.
      { iPureIntro. clear -Ht. lia. }
      iDestruct (big_sepM_lookup with "Hqvk") as (ridsqv) "[Hvk %Hridsqv]"; first apply Hv.
      (* From [Hvk] and [Hioa] we obtain a overlapped replica that (1) validates *)
      (* [ts] and (2) invalidates [ts] or observes [ts] to have aborted. *)
      destruct (cquorums_overlapped _ _ _ Hqrm Hridsqv) as (rid & Hinq & Hinqv).
      iDestruct (big_sepS_elem_of with "Hioa") as "Hrioa"; first apply Hinq.
      iNamed "Hrioa".
      iDestruct (big_sepS_elem_of with "Hvk") as "Hrvk"; first apply Hinqv.
      iDestruct (replica_key_validation_lb_lookup with "Hrvk Hvdl") as %Hvd.
      { clear -Ht Hlenvdl. lia. }
      iDestruct (big_sepL_lookup with "Habtifp") as "Habtgroup"; first apply Hvd.
      iSpecialize ("Habtgroup" with "[]").
      { iPureIntro.
        split; last done.
        clear -Ht. lia.
      }
      (* Derive txn abortedness from group abortedness. *)
      iAssert (is_txn_aborted γ t)%I as "#Habttxn".
      { do 2 iNamed "Hgroup".
        iDestruct (group_commit_lookup with "Hcm Habtgroup") as %Habtgroup.
        assert (Habtg : stm !! t = Some StAborted).
        { rewrite Hcm lookup_omap_Some in Habtgroup.
          destruct Habtgroup as (st & Hfalse & Hst).
          by destruct st.
        }
        by iDestruct (big_sepM_lookup with "Hsafestm") as "Habt"; first apply Habtg.
      }
      (* Derive contradiction from [is_txn_aborted γ t] and [kmodc !! t = Some v]. *)
      iDestruct (txn_res_lookup with "Hresm Habttxn") as %Habted.
      iDestruct (cmtd_kmod_vslice_agree with "Hkmodcs Hkmodc") as %Hkmodc.
      { apply Hall. }
      by rewrite Hkmodc lookup_vslice /dual_lookup lookup_omap Habted in Hv.
    }
    (* Obtain a witness that the committed history has been extended to [ts], and [vl = vr]. *)
    iMod (key_inv_quorum_read with "Hqvfbts Hqikoa Hrepllb Hlnrzlb Hkey")
      as "(Hkey & #Hcmtd & %Heq)".
    { apply Hnz. }
    { apply Hltts. }
    { apply Hpts. }
    { apply Houtside. }
    { apply Hleall. }
    iDestruct (key_inv_hide_kmodc_kmodl_pts with "Hkey") as "Hkey".
    (* Re-establish [past_action_witness]. *)
    iAssert (past_action_witness γ (ActRead ts key))%I as "#Hpa"; first iFrame "Hcmtd".
    iCombine "Hpas Hpa" as "Hpas'".
    rewrite -big_sepL_snoc.
    (* Re-establish [conflict_free], [conflict_past], [cmtxn_in_past] w.r.t. read. *)
    pose proof (conflict_free_inv_read Hhead Hcf) as Hcf'.
    pose proof (conflict_past_inv_read Hhead Hcp) as Hcp'.
    pose proof (cmtxn_in_past_inv_read ts key Hcmtxn) as Hcmtxn'.
    by iFrame "∗ # %".
  Qed.

End inv.
