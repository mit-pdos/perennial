From Perennial.program_proof.rsm.distx Require Import prelude.

Lemma lookup_resm_to_tmods_Some resm ts wrs :
  resm_to_tmods resm !! ts = Some wrs ↔
  resm !! ts = Some (ResCommitted wrs).
Proof.
  rewrite /resm_to_tmods lookup_omap.
  destruct (resm !! ts) as [res |] eqn:Hres; last done.
  split; intros Hresm.
  - by destruct res as [wrsx |] eqn:Hwrsx; first inv Hresm.
  - by rewrite Hresm /=.
Qed.

Lemma lookup_resm_to_tmods_None resm ts :
  resm_to_tmods resm !! ts = None ↔
  resm !! ts = None ∨ resm !! ts = Some ResAborted.
Proof.
  split; intros Hresm.
  - destruct (resm !! ts) as [res |] eqn:Hres; last by left.
    destruct res as [wrs |]; last by right.
    exfalso.
    by rewrite /resm_to_tmods lookup_omap Hres in Hresm.
  - rewrite /resm_to_tmods lookup_omap.
    by destruct Hresm as [Hresm | Hresm]; rewrite Hresm.
Qed.

Lemma conflict_free_head_commit future tmods ts wrs1 wrs2 :
  head future = Some (ActCmt ts wrs1) ->
  tmods !! ts = Some wrs2 ->
  conflict_free future tmods ->
  wrs2 = wrs1.
Admitted.

Lemma conflict_free_le_all future tmods ts wrs :
  head future = Some (ActCmt ts wrs) ->
  conflict_free future tmods ->
  le_all ts (dom tmods).
Admitted.

Lemma ext_by_lnrz_inv_commit ts v cmtd lnrz kmodl :
  kmodl !! ts = Some v ->
  le_all ts (dom kmodl) ->
  ext_by_lnrz cmtd lnrz kmodl ->
  ext_by_lnrz (last_extend ts cmtd ++ [v]) lnrz (delete ts kmodl).
Proof.
  intros Hv Hles Hext.
  destruct Hext as (vlast & Hprefix & Hlast & Hlen & Hext).
  (* Obtain [length cmtd ≤ ts < length lnrz]. *)
  apply elem_of_dom_2 in Hv as Hts.
  apply Hlen in Hts.
  exists v.
  split.
  { (* Re-establish prefix. *)
    apply prefix_pointwise.
    intros i Hi.
    (* Obtain [i < S ts]. *)
    rewrite last_length last_extend_length_eq_n in Hi; [| set_solver | lia].
    destruct (decide (i < length cmtd)%nat) as [Hilt | Hige].
    { (* Case: before extension [i < length cmtd]. *)
      rewrite /last_extend Hlast /extend.
      rewrite -app_assoc lookup_app_l; last done.
      by apply prefix_lookup_lt.
    }
    rewrite Nat.nlt_ge in Hige.
    assert (is_Some (lnrz !! i)) as [u Hu].
    { rewrite lookup_lt_is_Some. lia. }
    assert (Higeweak : (pred (length cmtd) ≤ i)%nat) by lia.
    rewrite Hu.
    destruct (decide (i < ts)%nat) as [Hits | Hits].
    { (* Case: read-extension [i < ts]. *)
      specialize (Hext _ _ Higeweak Hu).
      rewrite lookup_app_l; last first.
      { by rewrite last_extend_length_eq_n; [| set_solver | lia]. }
      rewrite /last_extend Hlast /extend.
      rewrite lookup_app_r; last done.
      rewrite lookup_replicate.
      split; last lia.
      rewrite -Hext.
      apply prev_dbval_lt_all.
      intros n Hn.
      (* Obtain [ts ≤ n]. *)
      specialize (Hles _ Hn). simpl in Hles.
      (* Prove [i < n] by [i < ts] and [ts ≤ n]. *)
      lia.
    }
    (* Case: write-extension [i = ts]. *)
    assert (i = ts) by lia. clear Hits Hi. subst i.
    rewrite lookup_snoc_Some. right.
    split.
    { by rewrite last_extend_length_eq_n; [| set_solver | lia]. }
    specialize (Hext _ _ Higeweak Hu).
    by rewrite (prev_dbval_lookup _ _ _ _ Hv) in Hext.
  }
  split.
  { (* Re-establish last. *)
    by rewrite last_snoc.
  }
  split.
  { (* Re-establish len. *)
    intros n Hn.
    rewrite last_length last_extend_length_eq_n; [| set_solver | lia].
    rewrite dom_delete_L elem_of_difference not_elem_of_singleton in Hn.
    destruct Hn as [Hin Hne].
    specialize (Hlen _ Hin). simpl in Hlen.
    specialize (Hles _ Hin). simpl in Hles.
    lia.
  }
  (* Re-establish ext. *)
  intros t u Ht Hu.
  rewrite last_length last_extend_length_eq_n in Ht; [| set_solver | lia].
  erewrite prev_dbval_delete; [| lia | done | done].
  apply Hext; [lia | done].
Qed.

Lemma ext_by_cmtd_inv_commit repl cmtd kmodc ts v :
  ts ≠ O ->
  kmodc !! ts = None ->
  ext_by_cmtd repl cmtd kmodc ts ->
  ext_by_cmtd repl (last_extend ts cmtd ++ [v]) (<[ts := v]> kmodc) ts.
Proof.
  intros Hnz Hts Hext.
  rewrite /ext_by_cmtd Hts in Hext.
  destruct Hext as [[tsr Hext] Hlen].
  rewrite /ext_by_cmtd lookup_insert Hext last_extend_twice.
  destruct (decide (cmtd = [])) as [-> | Hnnil]; first done.
  do 2 f_equal.
  assert (tsr ≤ ts)%nat; last lia.
  specialize (Hlen Hnz).
  rewrite Hext in Hlen.
  etrans; last apply Hlen.
  by apply last_extend_length_ge_n.
Qed.

Lemma lnrz_txns_destined_inv_commit tids tmodcs tmodas resm ts wrs :
  ts ∈ dom tmodcs ->
  ts ∉ dom (resm_to_tmods resm) ->
  lnrz_txns_destined tids tmodcs tmodas resm ->
  lnrz_txns_destined tids (delete ts tmodcs) tmodas (<[ts:=ResCommitted wrs]> resm).
Proof.
  rewrite /lnrz_txns_destined.
  intros Htsin Htsnotin Hdst tsx Htsx.
  clear Htsin Htsnotin.
  specialize (Hdst _ Htsx). simpl in Hdst.
  rewrite dom_delete_L resm_to_tmods_insert_committed dom_insert_L.
  destruct Hdst as [[Hin Hnotin] | Hdst].
  { left. set_solver. }
  destruct Hdst as [[Hin Hnotin] | [Hin Hnotin]].
  { right. left.
    split; first done.
    admit.
  }
  destruct (decide (tsx = ts)) as [-> | Hne].
  { left. set_solver. }
  right. right. set_solver.
Admitted.

Section inv.
  Context `{!distx_ghostG Σ}.

  Lemma kmod_lnrz_update {γ k kmod1 kmod2} kmod :
    kmod_lnrz_half γ k kmod1 -∗
    kmod_lnrz_half γ k kmod2 ==∗
    kmod_lnrz_half γ k kmod ∗ kmod_lnrz_half γ k kmod.
  Admitted.

  Lemma kmod_lnrz_big_agree {γ keys kmods f} :
    dom kmods = keys ->
    ([∗ set] k ∈ keys, kmod_lnrz_half γ k (f k)) -∗
    ([∗ map] k ↦ kmod ∈ kmods, kmod_lnrz_half γ k kmod) -∗
    ⌜map_Forall (λ k kmod, kmod = f k) kmods⌝.
  Proof.
    iIntros (Hdom) "Hkeys Hkmods".
    rewrite -Hdom.
    rewrite big_sepS_big_sepM.
    iCombine "Hkmods Hkeys" as "Hkmods".
    rewrite -big_sepM_sep.
    iApply big_sepM_pure.
    iApply (big_sepM_impl with "Hkmods").
    iIntros "!>" (k kmod Hkmod) "[Hkmod Hf]".
    iApply (kmod_lnrz_agree with "Hf Hkmod").
  Qed.

  Lemma kmod_lnrz_big_agree_update {γ keys kmods f} f' :
    dom kmods = keys ->
    ([∗ set] k ∈ keys, kmod_lnrz_half γ k (f k)) -∗
    ([∗ map] k ↦ kmod ∈ kmods, kmod_lnrz_half γ k kmod) ==∗
    ([∗ set] k ∈ keys, kmod_lnrz_half γ k (f' k)) ∗
    ([∗ map] k ↦ kmod ∈ kmods, kmod_lnrz_half γ k (f' k) ∗ ⌜kmod = f k⌝).
  Proof.
    iIntros (Hdom) "Hkeys Hkmods".
    rewrite -Hdom.
    rewrite 2!big_sepS_big_sepM.
    iCombine "Hkmods Hkeys" as "Hkmods".
    rewrite -2!big_sepM_sep.
    iAssert (⌜map_Forall (λ k kmod, kmod = f k) kmods⌝)%I as %Heq.
    { iApply big_sepM_pure.
      iApply (big_sepM_impl with "Hkmods").
      iIntros "!>" (k kmod Hkmod) "[Hkmod Hf]".
      iApply (kmod_lnrz_agree with "Hf Hkmod").
    }
    iApply big_sepM_bupd.
    iApply (big_sepM_mono with "Hkmods").
    iIntros (k kmod Hkmod) "[Hkmod Hf]".
    iMod (kmod_lnrz_update (f' k) with "Hkmod Hf") as "[Hkmod Hf]".
    iFrame.
    iPureIntro.
    by specialize (Heq _ _ Hkmod).
  Qed.

  Lemma kmod_cmtd_update {γ k kmod1 kmod2} kmod :
    kmod_cmtd_half γ k kmod1 -∗
    kmod_cmtd_half γ k kmod2 ==∗
    kmod_cmtd_half γ k kmod ∗ kmod_cmtd_half γ k kmod.
  Admitted.

  Lemma kmod_cmtd_big_agree {γ keys kmods f} :
    dom kmods = keys ->
    ([∗ set] k ∈ keys, kmod_cmtd_half γ k (f k)) -∗
    ([∗ map] k ↦ kmod ∈ kmods, kmod_cmtd_half γ k kmod) -∗
    ⌜map_Forall (λ k kmod, kmod = f k) kmods⌝.
  Proof.
    iIntros (Hdom) "Hkeys Hkmods".
    rewrite -Hdom.
    rewrite big_sepS_big_sepM.
    iCombine "Hkmods Hkeys" as "Hkmods".
    rewrite -big_sepM_sep.
    iApply big_sepM_pure.
    iApply (big_sepM_impl with "Hkmods").
    iIntros "!>" (k kmod Hkmod) "[Hkmod Hf]".
    iApply (kmod_cmtd_agree with "Hf Hkmod").
  Qed.

  (* TODO: separate agree from update *)
  Lemma kmod_cmtd_big_agree_update {γ keys kmods f} f' :
    dom kmods = keys ->
    ([∗ set] k ∈ keys, kmod_cmtd_half γ k (f k)) -∗
    ([∗ map] k ↦ kmod ∈ kmods, kmod_cmtd_half γ k kmod) ==∗
    ([∗ set] k ∈ keys, kmod_cmtd_half γ k (f' k)) ∗
    ([∗ map] k ↦ kmod ∈ kmods, kmod_cmtd_half γ k (f' k) ∗ ⌜kmod = f k⌝).
  Proof.
    iIntros (Hdom) "Hkeys Hkmods".
    rewrite -Hdom.
    rewrite 2!big_sepS_big_sepM.
    iCombine "Hkmods Hkeys" as "Hkmods".
    rewrite -2!big_sepM_sep.
    iAssert (⌜map_Forall (λ k kmod, kmod = f k) kmods⌝)%I as %Heq.
    { iApply big_sepM_pure.
      iApply (big_sepM_impl with "Hkmods").
      iIntros "!>" (k kmod Hkmod) "[Hkmod Hf]".
      iApply (kmod_cmtd_agree with "Hf Hkmod").
    }
    iApply big_sepM_bupd.
    iApply (big_sepM_mono with "Hkmods").
    iIntros (k kmod Hkmod) "[Hkmod Hf]".
    iMod (kmod_cmtd_update (f' k) with "Hkmod Hf") as "[Hkmod Hf]".
    iFrame.
    iPureIntro.
    by specialize (Heq _ _ Hkmod).
  Qed.

  Lemma keys_inv_prepared_at_ts γ resm kmodls kmodcs wrs ts :
    dom wrs = dom kmodls ->
    resm !! ts = None ->
    all_prepared γ ts wrs -∗
    ([∗ map] key ↦ kmodl;kmodc ∈ kmodls;kmodcs,
       key_inv_no_kmodl_kmodc γ key kmodl kmodc) -∗
    txnres_auth γ resm -∗
    ([∗ set] gid ∈ gids_all, group_inv γ gid) -∗
    ([∗ map] key ↦ kmodl;kmodc ∈ kmodls;kmodcs,
       key_inv_with_tsprep_no_kmodl_kmodc γ key ts kmodl kmodc) ∗
    txnres_auth γ resm ∗
    ([∗ set] gid ∈ gids_all, group_inv γ gid).
  Proof.
    iIntros (Hdom Hnone) "#Hpreps Hkeys Hresm Hgroups".
    iApply (big_sepM2_impl_res with "Hkeys [Hresm Hgroups]").
    { iFrame. }
    iIntros (k kmodl kmodc Hkmodl Hkmodc) "!> Hkey [Hresm Hgroups]".
    assert (Hinwrs : k ∈ dom wrs).
    { by rewrite Hdom elem_of_dom. }
    iDestruct "Hpreps" as "[Hwrs Hpreps]".
    set gid := key_to_group k.
    iDestruct (big_sepS_elem_of _ _ gid with "Hpreps") as "Hprep".
    { by apply elem_of_ptgroups. }
    iDestruct (big_sepS_elem_of_acc _ _ gid with "Hgroups") as "[Hgroup HgroupsC]".
    { apply elem_of_key_to_group. }
    do 2 iNamed "Hgroup".
    iDestruct (txnprep_lookup with "Hpm Hprep") as %Hp.
    assert (is_Some (stm !! ts)) as [res Hres].
    { rewrite -elem_of_dom. apply elem_of_dom_2 in Hp. set_solver. }
    destruct res as [pwrs | |]; last first.
    { (* Case: Txn [ts] has already aborted. Contradiction. *)
      iDestruct ("Htks" $! log stm tpls with "[] []") as "Htk"; [done | done |].
      iDestruct (big_sepM_lookup with "Htk") as "Htkabt"; first apply Hres.
      iDestruct (txnres_lookup with "Hresm Htkabt") as %Habt.
      congruence.
    }
    { (* Case: Txn [ts] has already committed. Contradiction. *)
      iDestruct ("Htks" $! log stm tpls with "[] []") as "Htk"; [done | done |].
      iDestruct (big_sepM_lookup with "Htk") as "Htkcmt"; first apply Hres.
      iDestruct "Htkcmt" as (wrs') "Htkcmt".
      iDestruct (txnres_lookup with "Hresm Htkcmt") as %Hcmt.
      congruence.
    }
    iDestruct (big_sepM_lookup with "Hvp") as "Hpwrs"; first apply Hres.
    iDestruct "Hpwrs" as (wrs') "(Hwrs' & _ & %Hvw & %Hne & %Hpwrs)".
    iDestruct (txnwrs_receipt_agree with "Hwrs Hwrs'") as %->.
    assert (Hinpwrs : k ∈ dom pwrs).
    { rewrite Hpwrs /wrs_group.
      assert (Hgoal : k ∈ filter (λ k, key_to_group k = gid) (dom wrs)).
      { by rewrite elem_of_filter. }
      by rewrite filter_dom_L in Hgoal.
    }
    assert (is_Some (tpls !! k)) as [tpl Htpl].
    { pose proof (apply_cmds_dom _ _ _ Hrsm) as Hdomtpls.
      rewrite -elem_of_dom Hdomtpls.
      rewrite /valid_wrs in Hvw.
      (* solved with [Hinwrs] and [Hvw] *)
      set_solver.
    }
    iAssert (⌜Forall (λ c, valid_pts_of_command c) log⌝)%I as %Hvpts.
    { rewrite Forall_forall.
      iIntros (x Hx).
      iDestruct (log_cpool_incl with "Hlog Hcpool") as %Hsubsume.
      rewrite /cpool_subsume_log Forall_forall in Hsubsume.
      specialize (Hsubsume _ Hx).
      iDestruct (big_sepS_elem_of with "Hvc") as "Hc"; first apply Hsubsume.
      destruct x; [done | | done | done]. simpl.
      by iDestruct "Hc" as (?) "(_ & %Hvts & _)".
    }
    pose proof (pts_consistency _ Hvpts) as Hpts.
    specialize (Hpts _ _ _ _ _ _ Hrsm Hres Htpl Hinpwrs).
    (* Take [tuple_repl_half] from [Hrepls]. *)
    iDestruct (big_sepM_lookup_acc _ _ k tpl with "Hrepls") as "[[Hhist Hts] HreplsC]".
    { by rewrite /tpls_group map_lookup_filter_Some. }
    iDestruct (key_inv_no_kmodl_kmodc_unseal_tsprep with "Hkey") as (tsprep) "Hkey".
    (* Finally, deduce [tsprep = ts]. *)
    iAssert (⌜tsprep = ts⌝)%I as %->.
    { iNamed "Hkey".
      iDestruct (ts_repl_agree with "Htsprep Hts") as %Heq.
      by rewrite Hpts in Heq.
    }
    iDestruct ("HreplsC" with "[$Hhist $Hts]") as "Hrepls".
    iDestruct ("HgroupsC" with "[-Hresm Hkey]") as "Hgroups".
    { iFrame "∗ # %". }
    iFrame.
  Qed.

  Definition key_inv_after_commit
    γ (key : dbkey) (tsprep : nat) (kmodl kmodc : dbkmod) : iProp Σ :=
    ∃ v, let kmodl' := delete tsprep kmodl in
         let kmodc' := <[tsprep := v]> kmodc in
         key_inv_with_tsprep_no_kmodl_kmodc γ key tsprep kmodl' kmodc' ∗
         ⌜kmodl !! tsprep = Some v⌝.

  Lemma key_inv_commit γ kmodl kmodc ts k v :
    ts ≠ O ->
    le_all ts (dom kmodl) ->
    kmodl !! ts = Some v ->
    kmodc !! ts = None ->
    key_inv_with_tsprep_no_kmodl_kmodc γ k ts kmodl kmodc -∗
    key_inv_with_tsprep_no_kmodl_kmodc γ k ts (delete ts kmodl) (<[ts:=v]> kmodc).
  Proof.
    iIntros (Hnz Hles Hkmodl Hkmodc) "Hkey".
    iNamed "Hkey".
    iNamed "Hprop".
    pose proof (ext_by_lnrz_inv_commit _ _ _ _ _ Hkmodl Hles Hdiffl) as Hdiffl'.
    pose proof (ext_by_cmtd_inv_commit _ _ _ _ v Hnz Hkmodc Hdiffc) as Hdiffc'.
    iFrame "∗ # %".
    iPureIntro.
    by rewrite lookup_insert_ne.
  Qed.

  Lemma keys_inv_commit γ kmodls kmodcs ts :
    ts ≠ O ->
    map_Forall (λ _ kmodl, le_all ts (dom kmodl)) kmodls ->
    map_Forall (λ _ kmodl, is_Some (kmodl !! ts)) kmodls ->
    map_Forall (λ _ kmodc, kmodc !! ts = None) kmodcs ->
    ([∗ map] key ↦ kmodl;kmodc ∈ kmodls;kmodcs,
       key_inv_with_tsprep_no_kmodl_kmodc γ key ts kmodl kmodc) -∗
    ([∗ map] key ↦ kmodl;kmodc ∈ kmodls;kmodcs,
       key_inv_after_commit γ key ts kmodl kmodc).
  Proof.
    iIntros (Hnz Hles Hkmodls Hkmodcs) "Hkeys".
    iApply (big_sepM2_impl with "Hkeys").
    iIntros (k kmodl kmodc Hkmodl Hkmodc) "!> Hkey".
    specialize (Hkmodls _ _ Hkmodl). simpl in Hkmodls.
    specialize (Hles _ _ Hkmodl). simpl in Hles.
    specialize (Hkmodcs _ _ Hkmodc). simpl in Hkmodcs.
    destruct Hkmodls as [v Hv].
    iExists v.
    iSplit; last done.
    by iApply key_inv_commit.
  Qed.

  (**
   * The commit action modifies the following logical states in [txn_inv]:
   * 1. Result map [resm].
   * 2. Will-commit transaction map [tmodcs].
   * 3. Key modification map by committed txns [kmodcs].
   * 4. Key modification map by linearized txns [kmodls].
   * Invariants to re-establish:
   * 1. Committed implies prepared [Hcip].
   * 2. Consistency between result map and committed kmod map [Htkcc].
   * 3. Consistency between result map and linearized kmod map [Htkcl].
   * 4. Conflict free [Hcf].
   *
   * And the following logical states in [key_inv]:
   * 1. Committed history [cmtd].
   * 2. Key modification by committed txns [kmodc].
   * 3. Key modification by linearized txns [kmodl].
   * Invariants to re-establish:
   * 1. Committed history is a prefix of linearized history [Hprefix].
   * 2. Difference between linearized and committed histories [Hdiffl].
   * 3. Difference between committed and replicated histories [Hdiffc].
   * 4. Not written at timestamp 0 [Hzrsv].
   *
   * It seems like we're missing an invariant that proves the committing
   * transaction must have linearized. We might want to add something like
   * prepared-implies-linearized-or-finalized.
   *)

  Lemma txn_inv_commit γ tid wrs future :
    head future = Some (ActCmt tid wrs) ->
    txns_lnrz_receipt γ tid -∗
    all_prepared γ tid wrs -∗
    txn_inv_no_future γ future -∗
    ([∗ set] gid ∈ gids_all, group_inv γ gid) -∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ==∗
    txn_inv_no_future γ (tail future) ∗
    ([∗ set] gid ∈ gids_all, group_inv γ gid) ∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    txnres_cmt γ tid wrs.
  Proof.
    iIntros (Hhead) "#Htid #Hprep Htxnsys Hgroups Hkeys".
    iNamed "Htxnsys".
    iDestruct (txns_lnrz_elem_of with "Htxnsl Htid") as %Htid.
    apply Hdest in Htid as Hcases.
    destruct Hcases as [[Hresm Hnotin] | Hcases].
    { (* Case: Txn [tid] has already aborted or committed. *)
      rewrite elem_of_dom in Hresm.
      destruct Hresm as [wrsc Hwrs].
      rewrite lookup_resm_to_tmods_Some in Hwrs.
      iDestruct (big_sepM_lookup with "Hvr") as "#Hres"; first apply Hwrs.
      iAssert (⌜wrsc = wrs⌝)%I as %->.
      { iDestruct "Hres" as "[Hwrsc _]".
        iDestruct "Hprep" as "[Hwrs _]".
        by iDestruct (txnwrs_receipt_agree with "Hwrs Hwrsc") as %?.
      }
      (* Case: Txn [tid] has already committed. Extract a witness without any update. *)
      iDestruct (txnres_witness with "Hresm") as "#Hcmt"; first apply Hwrs.
      unshelve epose proof (conflict_free_inv_commit_committed _ _ _ _ _ Hhead Hcf) as Hcf'.
      { apply not_elem_of_dom_1, Hnotin. }
      unshelve epose proof (conflict_past_inv_commit _ _ _ _ _ Hhead Hcp) as Hcp'.
      by iFrame "∗ # %".
    }
    destruct Hcases as [[Htmodas Hnotin] | [Htmodcs Hnotin]].
    { (* Case: Txn [tid] predicted to abort. Contradiction. *)
      (* Case A: [tid] not showing at all in [future] -> contradicting [Hhead]. *)
      (* Case B: [(tid, wrs)] conflicting with prior action -> add txnsys invs
      ReadLength and CommitLength and key inv constraining the length of
      replicated history with prepare timestamp. To show that [tid] is not
      committed nor aborted, we use [Hnotin] for the former, and
      [all_prepared_some_aborted_false] for the later. *)
      (* Case C: [(tid, wrs)] does not satisfy [P wrs]. Contradiction with
      additional premise. *)
      admit.
    }
    (* Case: Txn [tid] predicted to commit. Update states and extract commitment witness. *)
    (* Obtain [resm !! ts = None]. *)
    rewrite not_elem_of_dom lookup_resm_to_tmods_None in Hnotin.
    destruct Hnotin as [Hnone | Habt]; last first.
    { iDestruct (big_sepM_lookup with "Hvr") as "Habt"; first apply Habt.
      iDestruct (all_prepared_some_aborted_false with "Hprep Habt") as %[].
    }
    (* Obtain [wrsx], the write set in the result map of [tid]. *)
    rewrite elem_of_dom in Htmodcs.
    destruct Htmodcs as [wrsx Hwrs].
    (* Obtain eq of write set between the predicted [wrs] and the [wrsx] in the result map. *)
    pose proof (conflict_free_head_commit _ _ _ _ _ Hhead Hwrs Hcf). subst wrsx.
    assert (Hdom : dom wrs ⊆ keys_all) by admit.
    (* Take [dom wrs] of [kmod_lnrz_half] and [kmod_cmtd_half]. *)
    iDestruct (big_sepS_subseteq_difference_1 _ _ (dom wrs) with "Hkmodls") as "[Hkmodls HkmodlsO]".
    { apply Hdom. }
    iDestruct (big_sepS_subseteq_difference_1 _ _ (dom wrs) with "Hkmodcs") as "[Hkmodcs HkmodcsO]".
    { apply Hdom. }
    (* Take [dom wrs] of [key_inv]. *)
    iDestruct (big_sepS_subseteq_acc _ _ (dom wrs) with "Hkeys") as "[Hkeys HkeysC]".
    { apply Hdom. }
    (* Extract [kmod_lnrz_half] and [kmod_cmtd_half] out of [key_inv]. *)
    iDestruct (keys_inv_extract_kmodl_kmodc with "Hkeys") as "Hkeys".
    iDestruct "Hkeys" as (kmodls kmodcs) "(Hkeys & Hkmodls' & Hkmodcs' & %Hdomkmodls)".
    iDestruct (big_sepM2_dom with "Hkeys") as %Hdomkmodcs.
    rewrite Hdomkmodls in Hdomkmodcs. symmetry in Hdomkmodcs.
    (* Agreement of [kmod_lnrz_half] and [kmod_cmtd_half] between [txn_inv] and [key_inv]. *)
    iDestruct (kmod_lnrz_big_agree with "Hkmodls Hkmodls'") as %Hkmodls.
    { apply Hdomkmodls. }
    iDestruct (kmod_cmtd_big_agree with "Hkmodcs Hkmodcs'") as %Hkmodcs.
    { apply Hdomkmodcs. }
    (* Agreement and update of [kmod_lnrz_half] and [kmod_cmtd_half]. *)
    set tmodcs' := delete tid tmodcs.
    iMod (kmod_lnrz_big_agree_update (λ k, vslice tmodcs' k) with
           "Hkmodls Hkmodls'") as "[Hkmodls Hkmodls']".
    { apply Hdomkmodls. }
    iAssert ([∗ map] k ↦ kmod ∈ kmodls, kmod_lnrz_half γ k (delete tid kmod))%I
      with "[Hkmodls']" as "Hkmodls'".
    { iApply (big_sepM_impl with "Hkmodls'").
      iIntros (k kmod Hkmod) "!> [Hkmods %Heq]".
      subst tmodcs'.
      by rewrite vslice_delete Heq.
    }
    set resm' := <[tid := ResCommitted wrs]> resm.
    iMod (kmod_cmtd_big_agree_update (λ k, vslice (resm_to_tmods resm') k) with "Hkmodcs Hkmodcs'")
      as "[Hkmodcs Hkmodcs']".
    { apply Hdomkmodcs. }
    iAssert ([∗ map] k ↦ kmod; v ∈ kmodcs; wrs, kmod_cmtd_half γ k (<[tid := v]> kmod))%I
      with "[Hkmodcs']" as "Hkmodcs'".
    { iApply (big_sepM_sepM2_impl with "Hkmodcs'"); first done.
      iIntros (k kmod v Hkmod Hv) "!> [Hkmods %Heq]".
      subst resm'.
      by rewrite resm_to_tmods_insert_committed (vslice_insert_Some _ _ _ _ _ Hv) Heq.
    }
    (* Prove that for all [key ∈ dom wrs], the lock must be currently granted to [tid]. *)
    iDestruct (keys_inv_prepared_at_ts with "Hprep Hkeys Hresm Hgroups")
      as "(Hkeys & Hresm & Hgroups)"; [done | done |].
    (* Prove for each [kmodl] and [kmodc], [is_Some (kmodl !! tid)] and [kmodc !! tid = None]. *)
    assert (Hkmodlstid : map_Forall (λ _ kmodl, is_Some (kmodl !! tid)) kmodls).
    { intros k kmodl Hkmodl.
      specialize (Hkmodls _ _ Hkmodl). simpl in Hkmodls.
      rewrite Hkmodls lookup_vslice /dual_lookup Hwrs.
      rewrite -elem_of_dom.
      apply elem_of_dom_2 in Hkmodl.
      set_solver.
    }
    assert (Hkmodcstid : map_Forall (λ _ kmodc, kmodc !! tid = None) kmodcs).
    { intros k kmodc Hkmodc.
      specialize (Hkmodcs _ _ Hkmodc). simpl in Hkmodcs.
      rewrite Hkmodcs lookup_vslice /dual_lookup.
      assert (Hresm : resm_to_tmods resm !! tid = None).
      { rewrite lookup_resm_to_tmods_None. by left. }
      by rewrite Hresm.
    }
    (* Re-establish [key_inv] w.r.t. commit. *)
    iDestruct (keys_inv_commit with "Hkeys") as "Hkeys".
    { by eapply Hnz, elem_of_dom_2. }
    { intros k kmodl Hkmodl.
      pose proof (conflict_free_le_all _ _ _ _ Hhead Hcf) as Hle.
      specialize (Hkmodls _ _ Hkmodl). simpl in Hkmodls.
      eapply set_Forall_subseteq; last apply Hle.
      rewrite Hkmodls.
      apply dom_vslice_subseteq.
    }
    { apply Hkmodlstid. }
    { apply Hkmodcstid. }
    iAssert ([∗ map] k ↦ kmodl;kmodc ∈ kmodls; kmodcs,
               ∃ v, kmod_cmtd_half γ k (<[tid := v]> kmodc) ∗ ⌜kmodl !! tid = Some v⌝)%I
      with "[Hkmodcs']" as "Hkmodcs'".
    { rewrite 2!big_sepM2_alt.
      iDestruct "Hkmodcs'" as "[_ Hkmodcs]".
      iSplit; first by rewrite Hdomkmodls Hdomkmodcs.
      iApply (big_sepM_impl_dom_eq with "Hkmodcs").
      { rewrite 2!dom_map_zip_with_L. set_solver. }
      iIntros (k kmodcv kmodlc Hkmodcv Hkmodlc) "!> Hkmodcv".
      destruct kmodcv as [kmodc v]. destruct kmodlc as [kmodl kmodc'].
      rewrite map_lookup_zip_Some in Hkmodcv. destruct Hkmodcv as [Hkmodc Hv].
      rewrite map_lookup_zip_Some in Hkmodlc. destruct Hkmodlc as [Hkmodl Hkmodc'].
      rewrite Hkmodc in Hkmodc'. symmetry in Hkmodc'. inv Hkmodc'.
      iFrame.
      iPureIntro.
      simpl.
      specialize (Hkmodls _ _ Hkmodl). simpl in Hkmodls.
      by rewrite Hkmodls lookup_vslice /dual_lookup Hwrs.
    }
    iAssert ([∗ set] k ∈ dom wrs, key_inv γ k)%I with "[Hkmodls' Hkmodcs' Hkeys]" as "Hkeys".
    { iDestruct (big_sepM_big_sepM2_1 _ _ kmodcs with "Hkmodls'") as "Hkmodls'".
      { by rewrite Hdomkmodls Hdomkmodcs. }
      iCombine "Hkmodls' Hkmodcs'" as "Hkmods".
      rewrite -big_sepM2_sep.
      iCombine "Hkeys Hkmods" as "Hkeys".
      rewrite -big_sepM2_sep.
      rewrite big_sepS_big_sepM.
      iApply (big_sepM2_sepM_impl with "Hkeys"); first done.
      iIntros (k kmodl kmodc v Hkmodl Hkmodc Hv) "!> (Hkey & Hkmodl & Hkmodc)".
      clear Hv v.
      iDestruct "Hkmodc" as (v) "[Hkmodc %Hv]".
      iDestruct "Hkey" as (v') "[Hkey %Hv']".
      rewrite Hv in Hv'. symmetry in Hv'. inv Hv'.
      iNamed "Hkey".
      iFrame "∗ #".
    }
    iDestruct ("HkeysC" with "Hkeys") as "Hkeys".
    (* Update the unmodified part of [kmod_lnrz_half]. *)
    iAssert ([∗ set] x ∈ (keys_all ∖ dom wrs), kmod_lnrz_half γ x (vslice tmodcs' x))%I
      with "[HkmodlsO]" as "HkmodlsO".
    { iApply (big_sepS_impl with "HkmodlsO").
      iIntros (k Hk) "!> Hkmod".
      subst tmodcs'.
      assert (Hnotinwrs : wrs !! k = None).
      { rewrite -not_elem_of_dom. set_solver. }
      by rewrite (vslice_delete_None _ _ _ _ Hwrs Hnotinwrs).
    }
    (* Update the unmodified part of [kmod_cmtd_half]. *)
    iAssert ([∗ set] x ∈ (keys_all ∖ dom wrs), kmod_cmtd_half γ x (vslice (resm_to_tmods resm') x))%I
      with "[HkmodcsO]" as "HkmodcsO".
    { iApply (big_sepS_impl with "HkmodcsO").
      iIntros (k Hk) "!> Hkmod".
      subst resm'.
      rewrite resm_to_tmods_insert_committed.
      assert (Hnotinwrs : wrs !! k = None).
      { rewrite -not_elem_of_dom. set_solver. }
      rewrite (vslice_insert_None _ _ _ _ _ Hnotinwrs); last first.
      { rewrite lookup_resm_to_tmods_None. by left. }
      done.
    }
    (* Combine the modified and unmodified parts of [kmod_lnrz_half] and [kmod_cmtd_half]. *)
    iDestruct (big_sepS_subseteq_difference_2 with "Hkmodls HkmodlsO") as "Hkmodls".
    { apply Hdom. }
    iDestruct (big_sepS_subseteq_difference_2 with "Hkmodcs HkmodcsO") as "Hkmodcs".
    { apply Hdom. }
    (* Add [(tid, ResCommitted wrs)] to [resm] and extract a witness. *)
    iMod (txnres_insert _ (ResCommitted wrs) with "Hresm") as "Hresm"; first apply Hnone.
    iDestruct (txnres_witness _ _ tid with "Hresm") as "#Hcmt".
    { by rewrite lookup_insert. }
    (* Re-establish [valid_res]. *)
    (* Re-establish [conflict_free] and [conflict_past]. *)
    pose proof (conflict_free_inv_commit _ _ _ _ Hhead Hcf) as Hcf'.
    pose proof (conflict_past_inv_commit _ _ _ _ _ Hhead Hcp) as Hcp'.
    iFrame "∗ # %".
    iModIntro.
    iSplit.
    { by iApply (big_sepM_insert_2 with "[Hprep] Hvr"). }
    
  Admitted.

End inv.
