From Perennial.program_proof.tulip Require Import prelude.
From Perennial.program_proof.tulip.invariance Require Import cmd.

Lemma ext_by_cmtd_inv_learn_commit repl cmtd kmod ts v :
  kmod !! O = None ->
  kmod !! ts = Some v ->
  ext_by_cmtd repl cmtd kmod ts ->
  ext_by_cmtd (last_extend ts repl ++ [v]) cmtd kmod O.
Proof.
  intros Hz Hts Hdiff.
  rewrite /ext_by_cmtd Hts in Hdiff.
  destruct Hdiff as [Hdiff _].
  rewrite /ext_by_cmtd Hz.
  (* by the time repl catches up cmtd, they are equal, hence using 0 here *)
  exists O.
  split; last done.
  by rewrite Hdiff {2}/last_extend last_snoc /extend /= app_nil_r.
Qed.

Section inv.
  Context `{!heapGS Σ}.
  Context `{!tulip_ghostG Σ}.

  Lemma keys_inv_committed γ p ts pwrs wrs histm :
    dom histm = dom pwrs ->
    pwrs ⊆ wrs ->
    is_txn_committed γ ts wrs -∗
    ([∗ map] key ↦ hist ∈ histm, key_inv_no_repl_no_tsprep γ key hist ts) -∗
    txnsys_inv γ p -∗
    ([∗ map] key ↦ hist; v ∈ histm; pwrs, key_inv_cmted_no_repl_tsprep γ key hist ts v) ∗
    txnsys_inv γ p.
  Proof.
    iIntros (Hdom Hwrs) "#Hcmt Hhistm Htxnsys".
    iApply (big_sepM_sepM2_impl_res with "Hhistm Htxnsys"); first done.
    iIntros "!>" (k h v Htpl Hv) "Hkey Htxnsys".
    do 2 iNamed "Htxnsys".
    iDestruct (txn_res_lookup with "Hresm Hcmt") as %Hresm.
    do 2 iNamed "Hkey".
    iDestruct (cmtd_kmod_vslice_agree with "Hkmodcs Hkmodc") as %Hkmodc.
    { apply Hall. }
    assert (Hwrsv : wrs !! k = Some v); first by eapply lookup_weaken.
    assert (Hkmodcv : kmodc !! ts = Some v).
    { subst kmodc. by eapply vslice_resm_to_tmods_committed_present. }
    iAssert (txnsys_inv γ p)%I with "[-Hkmodl Hkmodc Hdbv Hlnrz Hcmtd]" as "Htxnsys".
    { iFrame "∗ # %". }
    iFrame "∗ # %".
  Qed.

  Lemma txnsys_inv_has_prepared γ p gid ts wrs :
    gid ∈ ptgroups (dom wrs) ->
    is_txn_committed γ ts wrs -∗
    txnsys_inv γ p -∗
    is_group_prepared γ gid ts.
  Proof.
    iIntros (Hptg) "Hres Htxnsys".
    do 2 iNamed "Htxnsys".
    iDestruct (txn_res_lookup with "Hresm Hres") as %Hr.
    iDestruct (big_sepM_lookup with "Hvr") as "Hr"; first by apply Hr.
    iDestruct "Hr" as "[_ Hpreps]".
    iDestruct (big_sepS_elem_of with "Hpreps") as "Hprep"; first apply Hptg.
    iFrame "#".
  Qed.

  Lemma key_inv_learn_commit {γ ts wrs hists} k h v h' :
    hists !! k = Some h ->
    wrs !! k = Some v ->
    multiwrite ts wrs hists !! k = Some h' ->
    key_inv_cmted_no_repl_tsprep γ k h ts v -∗
    key_inv_no_repl_no_tsprep γ k h' O.
  Proof.
    iIntros (Hh Hv Hh') "Hkey".
    do 3 iNamed "Hkey".
    iFrame "∗ # %".
    iPureIntro.
    rewrite lookup_merge Hv Hh /= in Hh'.
    inv Hh'.
    split.
    { by destruct (last_extend _ _). }
    split.
    { apply lookup_lt_Some in Hrfirst as Hlen.
      rewrite lookup_app_l; last first.
      { rewrite last_extend_length; last done. clear -Hlen. lia. }
      by rewrite lookup_last_extend_l.
    }
    by apply ext_by_cmtd_inv_learn_commit.
  Qed.

  Lemma keys_inv_learn_commit {γ ts wrs hists} :
    ([∗ map] key ↦ hist; v ∈ hists; wrs, key_inv_cmted_no_repl_tsprep γ key hist ts v) -∗
    ([∗ map] key ↦ hist ∈ multiwrite ts wrs hists, key_inv_no_repl_no_tsprep γ key hist O).
  Proof.
    iIntros "Hkeys".
    iApply (big_sepM2_sepM_impl with "Hkeys").
    { apply multiwrite_dom. }
    iIntros "!>" (k h v h' Hh Hv Hh') "Hkey".
    by iApply (key_inv_learn_commit with "Hkey").
  Qed.

  Lemma group_inv_learn_commit γ p gid log cpool ts pwrs :
    txn_cpool_subsume_log cpool (log ++ [CmdCommit ts pwrs]) ->
    txnsys_inv γ p -∗
    ([∗ set] key ∈ keys_all, key_inv γ key) -∗
    group_inv_no_log_with_cpool γ gid log cpool ==∗
    txnsys_inv γ p ∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    group_inv_no_log_with_cpool γ gid (log ++ [CmdCommit ts pwrs]) cpool.
  Proof.
    iIntros (Hsubsume) "Htxnsys Hkeys Hgroup".
    pose proof Hsubsume as Hcscincl.
    rewrite /txn_cpool_subsume_log Forall_app Forall_singleton in Hsubsume.
    destruct Hsubsume as [Hsubsume Hc].
    do 2 iNamed "Hgroup".
    (* Obtain proof that [ts] has committed. *)
    iDestruct (big_sepS_elem_of with "Hsafecp") as "Hc"; first apply Hc.
    simpl.
    iDestruct "Hc" as (wrs) "(Hcmt & Hwrs & _ & %Hpwrs & %Hgid)".
    rewrite /group_inv_no_log_with_cpool.
    destruct (stm !! ts) as [st |] eqn:Hdup; last first.
    { (* Case: Empty state; contradiction---no prepare before commit. *) 
      iDestruct (txnsys_inv_has_prepared with "Hcmt Htxnsys") as "#Hst"; first apply Hgid.
      iDestruct (group_prep_lookup with "Hpm Hst") as %Hlookup.
      specialize (Hpmstm _ _ Hlookup). simpl in Hpmstm.
      by apply not_elem_of_dom in Hdup.
    }
    (* Case: Transaction prepared, aborted, or committed. *)
    destruct st as [pwrs' | |] eqn:Hst; last first.
    { (* Case: [StAborted]; contradiction. *)
      iDestruct (big_sepM_lookup with "Hsafestm") as "#Habt"; first apply Hdup.
      do 2 iNamed "Htxnsys".
      iDestruct (txn_res_lookup with "Hresm Hcmt") as "%Hcmt".
      iDestruct (txn_res_lookup with "Hresm Habt") as "%Habt".
      congruence.
    }
    { (* Case: [StCommitted]; no-op. *)
      iFrame "∗ # %".
      iPureIntro.
      assert (Hcmted : cm !! ts = Some true).
      { by rewrite Hcm lookup_omap Hdup. }
      by rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hcmted.
    }
    (* Case: [StPrepared wrs] *)
    assert (Hxfinal : cm !! ts = None).
    { by rewrite Hcm lookup_omap Hdup. }
    rewrite /group_inv_no_log_no_cpool.
    rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hxfinal.
    set cm' := insert _ _ cm.
    set histm' := multiwrite _ _ _.
    (* Obtain proof of valid prepared input. *)
    iDestruct (big_sepM_lookup with "Hsafestm") as "Hc"; first apply Hdup. simpl.
    iDestruct "Hc" as "[_ Hsafepwrs]".
    iDestruct "Hsafepwrs" as (wrs') "(Hwrs' & %Hvts & %Hvwrs & %Hne & %Hpwrs')".
    iDestruct (txn_wrs_agree with "Hwrs Hwrs'") as %->.
    rewrite -Hpwrs in Hpwrs'. subst pwrs'.
    (* Take the required keys invariants. *)
    iDestruct (big_sepS_subseteq_acc _ _ (dom pwrs) with "Hkeys") as "[Hkeys HkeysC]".
    { (* Prove [dom pwrs ⊆ keys_all] *)
      transitivity (dom wrs); last done.
      rewrite Hpwrs.
      apply dom_filter_subseteq.
    }
    (* Take the required history and prepare timestamp from the group invariant. *)
    iDestruct (big_sepM_dom_subseteq_difference _ _ (dom pwrs) with "Hhists")
      as (histm [Hdomhistmg Hinclhistmg]) "[Hhistm HhistmO]".
    { (* Prove [dom pwrs ⊆ dom (tpls_group gid tpls)]. *)
      pose proof (apply_cmds_dom log _ _ Hrsm) as Hdom.
      rewrite Hpwrs wrs_group_keys_group_dom filter_group_keys_group_dom Hdom.
      clear -Hvwrs. set_solver.
    }
    iDestruct (big_sepM_dom_subseteq_difference _ _ (dom pwrs) with "Hlocks")
      as (ptsm [Hdomptsmg Hinclptsmg]) "[Hptsm HptsmO]".
    { (* Prove [dom pwrs ⊆ dom (tpls_group gid tpls)]. *)
      pose proof (apply_cmds_dom log _ _ Hrsm) as Hdom.
      rewrite Hpwrs wrs_group_keys_group_dom filter_group_keys_group_dom Hdomptsm.
      clear -Hvwrs. set_solver.
    }
    (* Extract the replicated history and prepared timestamp from keys invariant. *)
    iDestruct (keys_inv_extract_repl_pts with "Hkeys")
      as (histmk ptsmk) "(Hkeys & Hhistmk & Hptsmk & %Hdomhistmk)".
    iDestruct (big_sepM2_dom with "Hkeys") as %Hdomptsmk.
    symmetry in Hdomptsmk. rewrite Hdomhistmk in Hdomptsmk.
    (* Agree on history map from the group and keys invariants. *)
    iDestruct (repl_hist_big_agree with "Hhistm Hhistmk") as %->.
    { by rewrite Hdomhistmg Hdomhistmk. }
    (* Extending the replicated history. *)
    iMod (repl_hist_big_update (multiwrite ts pwrs histm) with "Hhistm Hhistmk")
      as "[Hhistm Hhistmk]".
    { rewrite map_Forall2_forall.
      split; last by rewrite multiwrite_dom.
      intros k h1 h2 Hh1 Hh2.
      apply elem_of_dom_2 in Hh1 as Hv.
      rewrite Hdomhistmk elem_of_dom in Hv.
      destruct Hv as [v Hv].
      rewrite (multiwrite_modified Hv Hh1) in Hh2.
      inv Hh2.
      apply prefix_app_r, last_extend_prefix.
    }
    (* Agree on history map from the group and keys invariants. *)
    iDestruct (repl_ts_big_agree with "Hptsm Hptsmk") as %->.
    { by rewrite Hdomptsmg Hdomptsmk. }
    (* Reset the prepared timestamp. *)
    iMod (repl_ts_big_update (release pwrs ptsm) with "Hptsm Hptsmk") as "[Hptsm Hptsmk]".
    { by rewrite release_dom. }
    (* From [prepared_impl_locked] we know keys in [dom pwrs] must be locked by [ts]. *)
    iAssert ([∗ map] key ↦ hist ∈ histm, key_inv_no_repl_no_tsprep γ key hist ts)%I
      with "[Hkeys]" as "Hkeys".
    { iApply (big_sepM2_sepM_impl with "Hkeys"); first done.
      iIntros (k h t h' Hh Ht Hh') "!> Hkey".
      assert (Hk : k ∈ dom pwrs).
      { by rewrite -Hdomhistmg elem_of_dom. }
      specialize (Hpil _ _ _ Hdup Hk).
      assert (Hincl : ptsm ⊆ tspreps).
      { etrans; [apply Hinclptsmg | apply map_filter_subseteq]. }
      pose proof (lookup_weaken _ _ _ _ Ht Hincl) as Ht'.
      rewrite Hpil in Ht'.
      inv Ht'.
      (* Looks like [inv Ht'] also gives [h = h'], which is useful, but is that
      the expected behavior? *)
      done.
    }
    (* Prove txn [ts] has committed on [tpls]. *)
    iDestruct (keys_inv_committed with "Hcmt Hkeys Htxnsys") as "[Hkeys Htxnsys]".
    { apply Hdomhistmg. }
    { rewrite Hpwrs. apply map_filter_subseteq. }
    (* Prove safe extension used later to re-establish the RSM invariant. *)
    iAssert (⌜safe_extension ts pwrs hists⌝)%I as %Hsafeext.
    { iIntros (k h Hh).
      apply map_lookup_filter_Some in Hh as [Hh Hk]. simpl in Hk.
      assert (Hhistmk : histm !! k = Some h).
      { clear -Hinclhistmg Hdomhistmg Hh Hk.
        rewrite -Hdomhistmg elem_of_dom in Hk.
        destruct Hk as [h' Hh'].
        unshelve epose proof (lookup_weaken_inv _ _ _ _ _ Hh' _ Hh) as ->.
        { etrans; [apply Hinclhistmg | apply map_filter_subseteq]. }
        done.
      }
      apply elem_of_dom in Hk as [v Hpwrsk].
      iDestruct (big_sepM2_lookup with "Hkeys") as "Hkey".
      { apply Hhistmk. }
      { apply Hpwrsk. }
      do 3 iNamed "Hkey".
      iPureIntro.
      rewrite /ext_by_cmtd Hv in Hdiffc.
      by destruct Hdiffc as [_ ?].
    }
    (* Re-establish keys invariant w.r.t. updated tuples. *)
    iDestruct (keys_inv_learn_commit with "Hkeys") as "Hkeys".
    (* Put ownership of tuples back to keys invariant. *)
    iDestruct (keys_inv_merge_repl_pts (dom pwrs) with "[Hkeys] Hhistmk Hptsmk") as "Hkeys".
    { by rewrite multiwrite_dom. }
    { iApply (big_sepM_sepM2_impl with "Hkeys").
      { by rewrite release_dom multiwrite_dom Hdomhistmg Hdomptsmg. }
      iIntros (k h t Hh Ht) "!> Hkey".
      apply elem_of_dom_2 in Hh as Hinpwrs.
      rewrite multiwrite_dom Hdomhistmg in Hinpwrs.
      pose proof Hinpwrs as Hinptsm. rewrite -Hdomptsmg in Hinptsm.
      assert (Hunlocked : release pwrs ptsm !! k = Some O).
      { by apply release_modified. }
      by inv Hunlocked.
    }
    iDestruct ("HkeysC" with "Hkeys") as "Hkeys".
    (* Merge ownership of replicated history back to group invariant. *)
    iDestruct (repl_hist_multiwrite_disjoint ts pwrs with "HhistmO") as "HhistmO".
    { set_solver. }
    rewrite multiwrite_difference_distr.
    iDestruct (big_sepM_subseteq_difference_2 with "Hhistm HhistmO") as "Hhistm".
    { by apply multiwrite_mono. }
    rewrite multiwrite_filter_group_commute.
    (* Merge ownership of prepared timestamp back to group invariant. *)
    iDestruct (repl_ts_release_disjoint pwrs with "HptsmO") as "HptsmO".
    { set_solver. }
    rewrite release_difference_distr.
    iDestruct (big_sepM_subseteq_difference_2 with "Hptsm HptsmO") as "Hptsm".
    { by apply release_mono. }
    rewrite release_filter_group_commute.
    (* Insert [(ts, true)] into the commit map. *)
    iMod (group_commit_insert ts true with "Hcm") as "[Hcm _]".
    { apply Hxfinal. }
    (* Re-establish [safe_txnst]. *)
    iDestruct (big_sepM_insert_2 _ _ ts (StCommitted) with "[] Hsafestm") as "Hsafestm'".
    { iFrame "Hcmt". }
    iFrame "∗ # %".
    iPureIntro.
    split; first by case_decide.
    split.
    { rewrite dom_insert_L.
      apply (map_Forall_impl _ _ _ Hpmstm).
      intros t b Hb. clear -Hb.
      destruct b; [set_solver | done].
    }
    split.
    { by rewrite release_dom. }
    split.
    { by rewrite Hcm omap_insert /=. }
    split.
    { (* Re-establish [prepared_impl_locked]. *)
      intros t m k Hm Hk.
      destruct (decide (t = ts)) as [-> | Hneq]; first by rewrite lookup_insert_eq in Hm.
      rewrite lookup_insert_ne in Hm; last done.
      pose proof (Hpil _ _ _ Hm Hk) as Hkt.
      rewrite -Hkt release_unmodified; first done.
      apply not_elem_of_dom.
      intros Hinpwrs.
      specialize (Hpil _ _ _ Hdup Hinpwrs).
      rewrite Hpil in Hkt.
      clear -Hneq Hkt. inv Hkt.
    }
    split.
    { (* Re-establish [locked_impl_prepared]. *)
      intros k t Ht Hnz.
      destruct (decide (k ∈ dom pwrs)) as [Hin | Hnotin].
      { rewrite release_modified in Ht; last first.
        { rewrite Hdomptsm.
          rewrite /valid_wrs in Hvwrs.
          clear -Hin Hvwrs Hpwrs.
          assert (Hincl : dom pwrs ⊆ dom wrs).
          { rewrite Hpwrs. apply dom_filter_subseteq. }
          set_solver.
        }
        { apply Hin. }
        clear -Hnz Ht. inv Ht.
      }
      rewrite release_unmodified in Ht; last first.
      { by apply not_elem_of_dom. }
      specialize (Hlip _ _ Ht Hnz).
      destruct Hlip as (m & Hm & Hinm).
      exists m.
      destruct (decide (t = ts)) as [-> | Hneq]; last by rewrite lookup_insert_ne.
      exfalso.
      clear -Hm Hdup Hinm Hnotin.
      set_solver.
    }
    { rewrite lookup_insert_ne; first apply Htsnz.
      rewrite /valid_ts in Hvts.
      clear -Hvts. lia.
    }
  Qed.

End inv.
