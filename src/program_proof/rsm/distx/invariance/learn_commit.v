From Perennial.program_proof.rsm.distx Require Import prelude.

Lemma ext_by_cmtd_inv_learn_commit repl cmtd kmod ts v :
  kmod !! O = None ->
  kmod !! ts = Some v ->
  ext_by_cmtd repl cmtd kmod ts ->
  ext_by_cmtd (last_extend ts repl ++ [v]) cmtd kmod O.
Proof.
  intros Hz Hts Hdiff.
  rewrite /ext_by_cmtd Hts in Hdiff.
  rewrite /ext_by_cmtd Hz.
  split; last done.
  (* by the time repl catches up cmtd, they are equal, hence using 0 here *)
  exists O.
  by rewrite Hdiff {2}/last_extend last_snoc /extend /= app_nil_r.
Qed.

Section inv.
  Context `{!distx_ghostG Σ}.

  Lemma txn_tokens_inv_learn_commit γ gid log ts :
    (∃ wrs, txnres_cmt γ ts wrs) -∗
    txn_tokens γ gid log -∗
    txn_tokens γ gid (log ++ [CmdCmt ts]).
  Proof.
    iIntros "[%wrs Hcmt] Htks".
    iIntros (logp stmp tplsp Hprefix Hrsmp).
    destruct (prefix_snoc _ _ _ Hprefix) as [Hlogp | ->].
    { by iApply "Htks". }
    rewrite /apply_cmds foldl_snoc /= in Hrsmp.
    destruct (foldl _ _ _) eqn:Hrsm; last done.
    simpl in Hrsmp.
    destruct (txns !! ts) as [st |]; last done.
    destruct st as [pwrs | |] eqn:Hst; last done.
    { inversion Hrsmp. subst stmp.
      iApply (big_sepM_insert_2 with "[Hcmt] [Htks]"); first by iFrame.
      by iApply "Htks".
    }
    inversion Hrsmp. subst stmp.
    by iApply "Htks".
  Qed.

  Lemma keys_inv_committed γ p ts pwrs wrs tpls :
    dom tpls = dom pwrs ->
    pwrs ⊆ wrs ->
    map_Forall (λ _ t, t.2 = ts) tpls ->
    txnres_cmt γ ts wrs -∗
    ([∗ map] key ↦ tpl ∈ tpls, key_inv_no_repl_tsprep γ key tpl.1 tpl.2) -∗
    txnsys_inv γ p -∗
    ([∗ map] key ↦ tpl; v ∈ tpls; pwrs, key_inv_cmted_no_repl_tsprep γ key tpl.1 ts v) ∗
    txnsys_inv γ p.
  Proof.
    iIntros (Hdom Hwrs Hts) "#Hcmt Htpls Htxn".
    iApply (big_sepM_sepM2_impl_res with "Htpls Htxn"); first done.
    iIntros "!>" (k [l t] v Htpl Hv) "Hkey Htxn".
    simpl.
    iNamed "Htxn".
    iDestruct (txnres_lookup with "Hresm Hcmt") as %Hresm.
    iNamed "Hkey". iNamed "Hprop".
    iDestruct (kmod_cmtd_vslice_agree with "Hkmodcs Hkmodc") as %Hkmodc.
    { apply Hall. }
    assert (Hwrsv : wrs !! k = Some v); first by eapply lookup_weaken.
    assert (Hkmodcv : kmodc !! ts = Some v).
    { subst kmodc. by eapply vslice_resm_to_tmods_committed_present. }
    specialize (Hts _ _ Htpl). simpl in Hts. subst t.
    by iFrame "∗ # %".
  Qed.

  Lemma txnsys_inv_has_prepared γ p gid ts wrs :
    gid ∈ ptgroups (dom wrs) ->
    txnres_cmt γ ts wrs -∗
    txnsys_inv γ p -∗
    txnprep_prep γ gid ts.
  Proof.
    iIntros (Hptg) "Hres Htxn".
    iNamed "Htxn".
    iDestruct (txnres_lookup with "Hresm Hres") as %Hr.
    iDestruct (big_sepM_lookup with "Hvr") as "Hr"; first by apply Hr.
    iDestruct "Hr" as "[_ Hpreps]".
    iDestruct (big_sepS_elem_of with "Hpreps") as "Hprep"; first apply Hptg.
    iFrame "#".
  Qed.

  Lemma key_inv_learn_commit {γ ts wrs tpls} k x y v :
    tpls !! k = Some x ->
    wrs !! k = Some v ->
    multiwrite ts wrs tpls !! k = Some y ->
    key_inv_cmted_no_repl_tsprep γ k x.1 ts v -∗
    key_inv_no_repl_tsprep γ k y.1 y.2.
  Proof.
    iIntros (Hx Hv Hy) "Hkeys".
    iNamed "Hkeys". iNamed "Hkey". iNamed "Hprop".
    iFrame "∗ # %".
    iPureIntro.
    rewrite lookup_merge Hv Hx /= in Hy.
    destruct x as [x ts'].
    inversion_clear Hy.
    by apply ext_by_cmtd_inv_learn_commit.
  Qed.

  Lemma keys_inv_learn_commit {γ ts wrs tpls} :
    ([∗ map] key ↦ tpl; v ∈ tpls; wrs,
       key_inv_cmted_no_repl_tsprep γ key tpl.1 ts v) -∗
    ([∗ map] key ↦ tpl ∈ multiwrite ts wrs tpls,
       key_inv_no_repl_tsprep γ key tpl.1 tpl.2).
  Proof.
    iIntros "Hkeys".
    iApply (big_sepM2_sepM_impl with "Hkeys").
    { apply multiwrite_dom. }
    iIntros "!>" (k x y z Hx Hy Hz) "Hkey".
    by iApply (key_inv_learn_commit with "Hkey").
  Qed.

  Lemma tuple_repl_half_multiwrite_disjoint {γ} ts wrs tpls :
    dom tpls ## dom wrs ->
    ([∗ map] k↦tpl ∈ tpls, tuple_repl_half γ k tpl) -∗
    ([∗ map] k↦tpl ∈ multiwrite ts wrs tpls, tuple_repl_half γ k tpl).
  Proof.
    iIntros (Hdom) "Htpls".
    iApply (big_sepM_impl_dom_eq with "Htpls"); first apply multiwrite_dom.
    iIntros "!>" (k t1 t2 Ht1 Ht2) "Htpl".
    destruct (wrs !! k) as [v |] eqn:Hwrs.
    { apply elem_of_dom_2 in Ht1. apply elem_of_dom_2 in Hwrs. set_solver. }
    rewrite /multiwrite lookup_merge Hwrs Ht1 /= in Ht2.
    by inversion_clear Ht2.
  Qed.

  Lemma group_inv_learn_commit γ p gid log cpool ts :
    cpool_subsume_log cpool (log ++ [CmdCmt ts]) ->
    txnsys_inv γ p -∗
    ([∗ set] key ∈ keys_all, key_inv γ key) -∗
    group_inv_no_log_with_cpool γ gid log cpool ==∗
    txnsys_inv γ p ∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    group_inv_no_log_with_cpool γ gid (log ++ [CmdCmt ts]) cpool.
  Proof.
    iIntros (Hsubsume) "Htxn Hkeys Hgroup".
    rewrite /cpool_subsume_log Forall_app Forall_singleton in Hsubsume.
    destruct Hsubsume as [Hsubsume Hc].
    do 2 iNamed "Hgroup".
    (* Obtain proof that [ts] has committed. *)
    iDestruct (big_sepS_elem_of with "Hvc") as "Hc"; first apply Hc.
    iDestruct "Hc" as (wrsc) "[Hcmt %Hgid]".
    rewrite /group_inv_no_log_with_cpool.
    destruct (stm !! ts) eqn:Hdup; last first.
    { (* Case: Empty state; contradiction---no prepare before commit. *) 
      iDestruct (txnsys_inv_has_prepared with "Hcmt Htxn") as "#Hst"; first apply Hgid.
      assert (Hpm : pm !! ts = None).
      { rewrite -not_elem_of_dom. rewrite -not_elem_of_dom in Hdup. set_solver. }
      iDestruct (txnprep_lookup with "Hpm Hst") as %Hlookup.
      congruence.
    }
    (* Case: Transaction prepared, aborted, or committed. *)
    destruct t as [pwrs | |] eqn:Ht; last first.
    { (* Case: [StAborted]; contradiction. *)
      iDestruct ("Htks" $! log stm tpls with "[] []") as "Htk"; [done | done |].
      iDestruct (big_sepM_lookup with "Htk") as "#Habt".
      { apply Hdup. }
      simpl.
      iNamed "Htxn".
      iDestruct (txnres_lookup with "Hresm Hcmt") as "%Hcmt".
      iDestruct (txnres_lookup with "Hresm Habt") as "%Habt".
      congruence.
    }
    { (* Case: [StCommitted]; no-op. *)
      rewrite /group_inv_no_log_no_cpool.
      rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hdup.
      (* Create txn tokens for the new state. *)
      iDestruct (txn_tokens_inv_learn_commit with "[Hcmt] Htks") as "#Htks'".
      { by eauto. }
      (* Create witnesses for the replicated history. *)
      iDestruct (hist_repl_witnesses_inv_learn (CmdCmt ts) with "Hrepls Hhists") as "#Hhists'".
      { by rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hdup. }
      by iFrame "∗ #".
    }
    (* Case: [StPrepared wrs] *)
    rewrite /group_inv_no_log_no_cpool.
    rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hdup.
    set tpls' := multiwrite _ _ _.
    (* Obtain proof of valid prepared input. *)
    iDestruct (big_sepM_lookup with "Hvp") as "Hc"; first apply Hdup. simpl.
    iDestruct "Hc" as (wrs) "(Hwrs & %Hts & %Hpwrs)".
    (* Prove the previously prepare [wrs] is equal to the commit [wrsc]. *)
    iAssert (⌜wrsc = wrs⌝)%I as %->.
    { iNamed "Htxn".
      iDestruct (txnres_lookup with "Hresm Hcmt") as %Hresm.
      iDestruct (big_sepM_lookup with "Hvr") as "Hwrsc"; first apply Hresm.
      iDestruct "Hwrsc" as "[Hwrsc _]".
      by iDestruct (txnwrs_receipt_agree with "Hwrs Hwrsc") as %?.
    }
    (* Take the required keys invariants. *)
    iDestruct (big_sepS_subseteq_acc _ _ (dom pwrs) with "Hkeys") as "[Hkeys HkeysC]".
    { (* Prove [dom pwrs ⊆ keys_all] *)
      destruct Hpwrs as (Hvalid & _ & Hpwrs).
      transitivity (dom wrs); last done.
      rewrite Hpwrs.
      apply dom_filter_subseteq.
    }
    (* Take the required tuple ownerships from the group invariant. *)
    iDestruct (big_sepM_dom_subseteq_difference _ _ (dom pwrs) with "Hrepls")
      as (tplsg [Hdom Hsubseteq]) "[Hrepls HreplsO]".
    { (* Prove [dom pwrs ⊆ dom (tpls_group gid tpls)]. *)
      destruct Hpwrs as (Hvalid & _ & Hpwrs).
      pose proof (apply_cmds_dom log _ _ Hrsm) as Hdom.
      rewrite Hpwrs wrs_group_keys_group_dom tpls_group_keys_group_dom Hdom.
      set_solver.
    }
    (* Expose the replicated history and prepared timestamp from keys invariant. *)
    iDestruct (keys_inv_extract_repl_tsprep with "Hkeys") as (tplsk) "(Hkeys & Htpls & %Hdom')".
    (* Agree on tuples from the group and keys invariants. *)
    iDestruct (tuple_repl_big_agree with "Hrepls Htpls") as %->; first by rewrite -Hdom in Hdom'.
    clear Hdom'.
    (* Update the tuples (resetting the prepared timestamp and extending the history). *)
    iMod (tuple_repl_big_update (multiwrite ts pwrs tplsg) with "Hrepls Htpls") as "[Hrepls Htpls]".
    { by rewrite multiwrite_dom. }
    { intros k tpl1 tpl2 Htpl1 Htpl2.
      subst tpls'.
      apply elem_of_dom_2 in Htpl1 as Hv.
      rewrite Hdom elem_of_dom in Hv.
      destruct Hv as [v Hv].
      rewrite (multiwrite_modified Hv Htpl1) in Htpl2.
      inv Htpl2. simpl.
      apply prefix_app_r, last_extend_prefix.
    }
    (* Prove txn [ts] has committed on [tpls]. *)
    iAssert (⌜Forall (λ c, valid_pts_of_command c) log⌝)%I as %Hpts.
    { rewrite Forall_forall.
      iIntros (x Hx).
      rewrite Forall_forall in Hsubsume.
      specialize (Hsubsume _ Hx).
      iDestruct (big_sepS_elem_of with "Hvc") as "Hc"; first apply Hsubsume.
      destruct x; [done | | done | done]. simpl.
      by iDestruct "Hc" as (?) "(_ & %Hvts & _)".
    }
    iDestruct (keys_inv_committed with "Hcmt Hkeys Htxn") as "[Hkeys Htxn]".
    { apply Hdom. }
    { destruct Hpwrs as (_ & _ & Hpwrs). rewrite Hpwrs. apply map_filter_subseteq. }
    { (* Prove prepared timestamp of [tplsg] is [ts]. *)
      intros k tpl Hlookup.
      eapply (pts_consistency log); [apply Hpts | apply Hrsm | apply Hdup | |].
      { eapply lookup_weaken; first apply Hlookup.
        transitivity (tpls_group gid tpls); first done.
        rewrite /tpls_group.
        apply map_filter_subseteq.
      }
      { rewrite -Hdom. by eapply elem_of_dom_2. }
    }
    (* Re-establish keys invariant w.r.t. updated tuples. *)
    iDestruct (keys_inv_learn_commit with "Hkeys") as "Hkeys".
    (* Put ownership of tuples back to keys invariant. *)
    iDestruct (keys_inv_merge_repl_tsprep (dom pwrs) with "Hkeys Htpls") as "Hkeys".
    { by rewrite multiwrite_dom. }
    iDestruct ("HkeysC" with "Hkeys") as "Hkeys".
    (* Merge ownership of tuples back to group invariant. *)
    iDestruct (tuple_repl_half_multiwrite_disjoint ts pwrs with "HreplsO") as "HreplsO".
    { set_solver. }
    rewrite multiwrite_difference_distr.
    iDestruct (big_sepM_subseteq_difference_2 with "Hrepls HreplsO") as "Hrepls".
    { by apply multiwrite_mono. }
    rewrite multiwrite_tpls_group_commute.
    (* Create txn tokens for the new state. *)
    iDestruct (txn_tokens_inv_learn_commit with "[Hcmt] Htks") as "Htks'".
    { by eauto. }
    (* Create witnesses for the replicated history. *)
    iDestruct (hist_repl_witnesses_inv_learn (CmdCmt ts) with "Hrepls Hhists") as "#Hhists'".
    { by rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hdup. }
    (* Re-establish [valid_prepared]. *)
    iDestruct (big_sepM_insert_2 _ _ ts (StCommitted) with "[] Hvp") as "Hvp'".
    { by iDestruct (big_sepS_elem_of with "Hvc") as "Hc"; first apply Hc. }
    iFrame "∗ # %".
    by auto with set_solver.
  Qed.

End inv.
