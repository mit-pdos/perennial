From Perennial.program_proof.rsm.distx Require Import prelude.

Lemma ext_by_cmtd_inv_learn_abort {repl cmtd kmod} ts :
  kmod !! O = None ->
  kmod !! ts = None ->
  ext_by_cmtd repl cmtd kmod ts ->
  ext_by_cmtd repl cmtd kmod O.
Proof.
  intros Hz Hts Hdiff.
  rewrite /ext_by_cmtd Hts in Hdiff.
  rewrite /ext_by_cmtd Hz.
  by destruct Hdiff as [Hdiff _].
Qed.

Section inv.
  Context `{!distx_ghostG Σ}.

  Lemma txn_tokens_inv_learn_abort γ gid log ts :
    txnres_abt γ ts -∗
    txn_tokens γ gid log -∗
    txn_tokens γ gid (log ++ [CmdAbt ts]).
  Proof.
    iIntros "Habt Htks".
    iIntros (logp stmp tplsp Hprefix Hrsmp).
    destruct (prefix_snoc _ _ _ Hprefix) as [Hlogp | ->].
    { by iApply "Htks". }
    rewrite /apply_cmds foldl_snoc /= in Hrsmp.
    destruct (foldl _ _ _) eqn:Hrsm; last done.
    simpl in Hrsmp.
    destruct (txns !! ts) as [st |]; last first.
    { inversion_clear Hrsmp.
      iApply (big_sepM_insert_2 with "[Habt] [Htks]"); first by iFrame.
      by iApply "Htks".
    }
    destruct st as [pwrs | |] eqn:Hst; inversion Hrsmp; subst stmp.
    { iApply (big_sepM_insert_2 with "[Habt] [Htks]"); first by iFrame.
      by iApply "Htks".
    }
    by iApply "Htks".
  Qed.

  Lemma keys_inv_prepared γ p ts tpls :
    map_Forall (λ _ t, t.2 = ts) tpls ->
    txnres_abt γ ts -∗
    ([∗ map] key ↦ tpl ∈ tpls, key_inv_no_repl_tsprep γ key tpl.1 tpl.2) -∗
    txnsys_inv γ p -∗
    ([∗ map] key ↦ tpl ∈ tpls, key_inv_prepared_no_repl_tsprep γ key tpl.1 ts) ∗
    txnsys_inv γ p.
  Proof.
    iIntros (Hts) "#Habt Htpls Htxn".
    iApply (big_sepM_impl_res with "Htpls Htxn").
    iIntros "!>" (k [l t] Htpl) "Hkey Htxn". simpl.
    iNamed "Htxn".
    iDestruct (txnres_lookup with "Hresm Habt") as %Hresm.
    iNamed "Hkey". iNamed "Hprop".
    iDestruct (kmod_cmtd_vslice_agree with "Hkmodcs Hkmodc") as %Hkmodc.
    { apply Hall. }
    assert (Hnc : kmodc !! ts = None).
    { subst kmodc. by eapply vslice_resm_to_tmods_aborted. }
    specialize (Hts _ _ Htpl). simpl in Hts. subst t.
    by iFrame "∗ # %".
  Qed.

  Lemma key_inv_learn_abort {γ ts wrs tpls} k x y :
    tpls !! k = Some x ->
    release wrs tpls !! k = Some y ->
    is_Some (wrs !! k) ->
    key_inv_prepared_no_repl_tsprep γ k x.1 ts -∗
    key_inv_no_repl_tsprep γ k y.1 y.2.
  Proof.
    iIntros (Hx Hy Hv) "Hkeys".
    iNamed "Hkeys". iNamed "Hkey". iNamed "Hprop".
    iFrame "∗ # %".
    iPureIntro.
    destruct Hv as [v Hv].
    rewrite lookup_merge Hx Hv /= in Hy.
    destruct x as [h t].
    inversion_clear Hy.
    by apply (ext_by_cmtd_inv_learn_abort ts).
  Qed.

  Lemma keys_inv_learn_abort {γ ts wrs tpls} :
    dom tpls = dom wrs ->
    ([∗ map] key ↦ tpl ∈ tpls,
       key_inv_prepared_no_repl_tsprep γ key tpl.1 ts) -∗
    ([∗ map] key ↦ tpl ∈ release wrs tpls,
       key_inv_no_repl_tsprep γ key tpl.1 tpl.2).
  Proof.
    iIntros (Hdom) "Hkeys".
    iApply (big_sepM_impl_dom_eq with "Hkeys").
    { apply release_dom. }
    iIntros "!>" (k x y Hx Hy) "Hkey".
    assert (is_Some (wrs !! k)) as Hwrs.
    { apply elem_of_dom_2 in Hx.
      rewrite set_eq in Hdom.
      by rewrite Hdom elem_of_dom in Hx.
    }
    by iApply (key_inv_learn_abort with "Hkey").
  Qed.

  Lemma tuple_repl_half_release_disjoint {γ} wrs tpls :
    dom tpls ## dom wrs ->
    ([∗ map] k↦tpl ∈ tpls, tuple_repl_half γ k tpl) -∗
    ([∗ map] k↦tpl ∈ release wrs tpls, tuple_repl_half γ k tpl).
  Proof.
    iIntros (Hdom) "Htpls".
    iApply (big_sepM_impl_dom_eq with "Htpls"); first apply release_dom.
    iIntros "!>" (k t1 t2 Ht1 Ht2) "Htpl".
    destruct (wrs !! k) as [v |] eqn:Hwrs.
    { apply elem_of_dom_2 in Ht1. apply elem_of_dom_2 in Hwrs. set_solver. }
    rewrite /release lookup_merge Hwrs Ht1 /= in Ht2.
    by inversion_clear Ht2.
  Qed.

  Lemma group_inv_learn_abort γ p gid log cpool ts :
    cpool_subsume_log cpool (log ++ [CmdAbt ts]) ->
    txnsys_inv γ p -∗
    ([∗ set] key ∈ keys_all, key_inv γ key) -∗
    group_inv_no_log_with_cpool γ gid log cpool ==∗
    txnsys_inv γ p ∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    group_inv_no_log_with_cpool γ gid (log ++ [CmdAbt ts]) cpool.
  Proof.
    iIntros (Hsubsume) "Htxn Hkeys Hgroup".
    rewrite /cpool_subsume_log Forall_app Forall_singleton in Hsubsume.
    destruct Hsubsume as [Hsubsume Hc].
    do 2 iNamed "Hgroup".
    (* Obtain proof that [ts] has aborted. *)
    iDestruct (big_sepS_elem_of _ _ _ Hc with "Hvc") as "[Habt _]".
    rewrite /group_inv_no_log_with_cpool.
    destruct (stm !! ts) as [st |] eqn:Hdup; last first.
    { (* Case: Directly abort without prepare. *)
      rewrite /group_inv_no_log_no_cpool.
      rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hdup.
      (* Create txn tokens for the new state. *)
      iDestruct (txn_tokens_inv_learn_abort with "Habt Htks") as "Htks'".
      (* Create witnesses for the replicated history. *)
      iDestruct (hist_repl_witnesses_inv_learn (CmdAbt ts) with "Hrepls Hhists") as "#Hhists'".
      { by rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hdup. }
      (* Re-establish [valid_prepared]. *)
      iDestruct (big_sepM_insert_2 _ _ ts StAborted with "[] Hvp") as "Hvp'".
      { done. }
      iFrame "∗ # %".
      by auto with set_solver.
    }
    (* Case: Txn [ts] has prepared, aborted, or committed. *)
    rewrite /group_inv_no_log_no_cpool.
    rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hdup.
    destruct st as [pwrs | |] eqn:Ht; first 1 last.
    { (* Case: Committed; contradiction by obtaining a commit token. *)
      iDestruct ("Htks" $! log stm tpls with "[] []") as "Htk"; [done | done |].
      iDestruct (big_sepM_lookup with "Htk") as "Hcmt"; first apply Hdup. simpl.
      iDestruct "Hcmt" as (wrs) "Hcmt".
      iNamed "Htxn".
      iDestruct (txnres_lookup with "Hresm Habt") as %Habt.
      iDestruct (txnres_lookup with "Hresm Hcmt") as %Hcmt.
      congruence.
    }
    { (* Case: Aborted; no-op. *)
      (* Create txn tokens for the new state. *)
      iDestruct (txn_tokens_inv_learn_abort with "Habt Htks") as "Htks'".
      (* Create witnesses for the replicated history. *)
      iDestruct (hist_repl_witnesses_inv_learn (CmdAbt ts) with "Hrepls Hhists") as "#Hhists'".
      { by rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hdup. }
      by iFrame "∗ # %".
    }
    (* Case: Prepared; release the locks on tuples. *)
    set tpls' := release _ _.
    (* Obtain proof of valid prepared input. *)
    iDestruct (big_sepM_lookup with "Hvp") as "Hc"; first apply Hdup. simpl.
    iDestruct "Hc" as (wrs) "(Hwrs & %Hts & %Hpwrs)".
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
    (* Update the tuples (resetting the prepared timestamp). *)
    iMod (tuple_repl_big_update (release pwrs tplsg) with "Hrepls Htpls") as "[Hrepls Htpls]".
    { by rewrite release_dom. }
    { intros k tpl1 tpl2 Htpl1 Htpl2.
      subst tpls'.
      apply elem_of_dom_2 in Htpl1 as Hsome.
      rewrite Hdom elem_of_dom in Hsome.
      rewrite (release_modified Hsome Htpl1) in Htpl2.
      by inv Htpl2.
    }
    (* Prove txn [ts] has prepared but not committed on [tpls]. *)
    iAssert (⌜Forall (λ c, valid_pts_of_command c) log⌝)%I as %Hpts.
    { rewrite Forall_forall.
      iIntros (x Hx).
      rewrite Forall_forall in Hsubsume.
      specialize (Hsubsume _ Hx).
      iDestruct (big_sepS_elem_of with "Hvc") as "Hc"; first apply Hsubsume.
      destruct x; [done | | done | done]. simpl.
      by iDestruct "Hc" as (?) "(_ & %Hvts & _)".
    }
    iDestruct (keys_inv_prepared with "Habt Hkeys Htxn") as "[Hkeys Htxn]".
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
    iDestruct (keys_inv_learn_abort with "Hkeys") as "Hkeys"; first apply Hdom.
    (* Put ownership of tuples back to keys invariant. *)
    iDestruct (keys_inv_merge_repl_tsprep (dom pwrs) with "Hkeys Htpls") as "Hkeys".
    { by rewrite release_dom. }
    iDestruct ("HkeysC" with "Hkeys") as "Hkeys".
    (* Merge ownership of tuples back to group invariant. *)
    iDestruct (tuple_repl_half_release_disjoint pwrs with "HreplsO") as "HreplsO".
    { set_solver. }
    rewrite release_difference_distr.
    iDestruct (big_sepM_subseteq_difference_2 with "Hrepls HreplsO") as "Hrepls".
    { by apply release_mono. }
    rewrite release_tpls_group_commute.
    (* Create txn tokens for the new state. *)
    iDestruct (txn_tokens_inv_learn_abort with "Habt Htks") as "Htks'".
    (* Create witnesses for the replicated history. *)
    iDestruct (hist_repl_witnesses_inv_learn (CmdAbt ts) with "Hrepls Hhists") as "#Hhists'".
    { by rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hdup. }
    (* Re-establish [valid_prepared]. *)
    iDestruct (big_sepM_insert_2 _ _ ts StAborted with "[] Hvp") as "Hvp'".
    { by iDestruct (big_sepS_elem_of with "Hvc") as "Hc"; first apply Hc. }
    iFrame "∗ # %".
    by auto with set_solver.
  Qed.

End inv.
