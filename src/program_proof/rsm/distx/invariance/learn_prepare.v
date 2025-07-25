From Perennial.program_proof.rsm.distx Require Import prelude.
From Perennial.program_proof.rsm.distx.invariance Require Import abort.

Lemma ext_by_cmtd_inv_learn_prepare repl cmtd kmod ts :
  kmod !! O = None ->
  (length repl ≤ ts)%nat ->
  kmod !! ts = None ->
  ext_by_cmtd repl cmtd kmod O ->
  ext_by_cmtd repl cmtd kmod ts.
Proof.
  intros Hz Hlen Hts Hdiff.
  rewrite /ext_by_cmtd Hz in Hdiff.
  destruct Hdiff as [[tsrd Hextend] _].
  rewrite /ext_by_cmtd Hts.
  by split; first eauto.
Qed.

Section inv.
  Context `{!distx_ghostG Σ}.

  Lemma txn_tokens_inv_learn_prepare_noop {γ gid log stm tpls ts} pwrs :
    apply_cmds log = State stm tpls ->
    is_Some (stm !! ts) ->
    txn_tokens γ gid log -∗
    txn_tokens γ gid (log ++ [CmdPrep ts pwrs]).
  Proof.
    iIntros (Hrsm Hstm) "Htks".
    iIntros (logp stmp tplsp Hprefix Hrsmp).
    destruct (prefix_snoc _ _ _ Hprefix) as [Hlogp | ->].
    { by iApply "Htks". }
    destruct Hstm as [st Hstm].
    rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hstm in Hrsmp.
    inversion Hrsmp. subst stmp.
    by iApply "Htks".
  Qed.

  Lemma txn_tokens_inv_learn_prepare_prepared γ gid log stm tpls ts pwrs :
    apply_cmds log = State stm tpls ->
    validate ts pwrs tpls = true ->
    txnprep_prep γ gid ts -∗
    txn_tokens γ gid log -∗
    txn_tokens γ gid (log ++ [CmdPrep ts pwrs]).
  Proof.
    iIntros (Hrsm Hvd) "Hprep Htks".
    destruct (stm !! ts) eqn:Hstm.
    { by iDestruct (txn_tokens_inv_learn_prepare_noop pwrs with "Htks") as "Htks". }
    iIntros (logp stmp tplsp Hprefix Hrsmp).
    destruct (prefix_snoc _ _ _ Hprefix) as [Hlogp | ->].
    { by iApply "Htks". }
    rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hstm Hvd in Hrsmp.
    inversion Hrsmp. subst stmp.
    iApply (big_sepM_insert_2 with "[Hprep] [Htks]"); first done.
    by iApply "Htks".
  Qed.

  Lemma txn_tokens_inv_learn_prepare_aborted γ gid log stm tpls ts pwrs :
    apply_cmds log = State stm tpls ->
    validate ts pwrs tpls = false ->
    txnres_abt γ ts -∗
    txn_tokens γ gid log -∗
    txn_tokens γ gid (log ++ [CmdPrep ts pwrs]).
  Proof.
    iIntros (Hrsm Hvd) "Habt Htks".
    destruct (stm !! ts) eqn:Hstm.
    { by iDestruct (txn_tokens_inv_learn_prepare_noop pwrs with "Htks") as "Htks". }
    iIntros (logp stmp tplsp Hprefix Hrsmp).
    destruct (prefix_snoc _ _ _ Hprefix) as [Hlogp | ->].
    { by iApply "Htks". }
    rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hstm Hvd in Hrsmp.
    inversion Hrsmp. subst stmp.
    iApply (big_sepM_insert_2 with "[Habt] [Htks]"); first done.
    by iApply "Htks".
  Qed.

  Lemma txnsys_inv_learn_prepare_failed γ p ts :
    some_aborted γ ts -∗
    txnsys_inv γ p ==∗
    txnsys_inv γ p ∗
    txnres_abt γ ts.
  Proof.
    iIntros "#Habt Htxn".
    iNamed "Htxn".
    destruct (resm !! ts) as [res |] eqn:Hres; last first.
    { (* Case: [ts] has neither aborted nor committed yet. *)
      iMod (txnres_insert ts ResAborted with "Hresm") as "Hresm"; first done.
      iDestruct (txnres_witness with "Hresm") as "#Hreceipt".
      { apply lookup_insert_eq. }
      iFrame "∗ # %".
      iNamed "Hpart".
      rewrite /partitioned_tids resm_to_tmods_insert_aborted; last by left.
      rewrite big_sepM_insert; last done.
      iFrame "∗ #".
      iPureIntro.
      split; first set_solver.
      rewrite /cmtxn_in_past resm_to_tmods_insert_aborted; last by left.
      split; last done.
      intros t m Htm.
      specialize (Htidcs _ _ Htm). simpl in Htidcs.
      destruct Htidcs as [? | Hresmc]; first by left.
      destruct (decide (t = ts)) as [-> | Hne].
      { by rewrite Hresmc in Hres. }
      by rewrite lookup_insert_ne; first right.
    }
    destruct res as [wrsc |]; last first.
    { (* Case: [ts] aborted; get a witness without any update. *)
      iDestruct (txnres_witness with "Hresm") as "#Hreceipt"; first apply Hres.
      by iFrame "∗ # %".
    }
    (* Case: [ts] committed; contradiction. *)
    iDestruct (big_sepM_lookup with "Hvr") as "#Hprep"; first apply Hres.
    iDestruct (all_prepared_some_aborted with "Hprep Habt") as %[].
  Qed.

  Lemma key_inv_not_committed γ p gid ts pm key kmodc tpl :
    gid = key_to_group key ->
    pm !! ts = None ->
    txnprep_auth γ gid pm -∗
    txnsys_inv γ p -∗
    key_inv_with_kmodc_no_repl_tsprep γ key kmodc tpl.1 tpl.2 -∗
    ⌜kmodc !! ts = None⌝.
  Proof.
    iIntros (Hgid Hnone) "Hpm Htxn Hkey".
    iNamed "Htxn".
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
          iDestruct (txnprep_lookup with "Hpm Hprep") as %Hprep.
          congruence.
        }
        (* Case: [key] not in the write set of [ts]. *)
        iNamed "Hkey". iNamed "Hprop".
        iDestruct (kmod_cmtd_vslice_agree with "Hkmodcs Hkmodc") as %Hkmodc.
        { apply Hall. }
        iPureIntro.
        subst kmodc.
        by eapply vslice_resm_to_tmods_committed_absent.
      }
      { (* Case: Aborted. *)
        iNamed "Hkey". iNamed "Hprop".
        iDestruct (kmod_cmtd_vslice_agree with "Hkmodcs Hkmodc") as %Hkmodc.
        { apply Hall. }
        iPureIntro.
        subst kmodc.
        by eapply vslice_resm_to_tmods_aborted.
      }
    }
    (* Case: Not committed or aborted. *)
    iNamed "Hkey". iNamed "Hprop".
    iDestruct (kmod_cmtd_vslice_agree with "Hkmodcs Hkmodc") as %Hkmodc.
    { apply Hall. }
    iPureIntro.
    subst kmodc.
    by eapply vslice_resm_to_tmods_not_terminated.
  Qed.

  Lemma keys_inv_not_committed γ p gid ts pm tpls :
    set_Forall (λ k, key_to_group k = gid) (dom tpls) ->
    pm !! ts = None ->
    ([∗ map] key ↦ tpl ∈ tpls, key_inv_no_repl_tsprep γ key tpl.1 tpl.2) -∗
    txnprep_auth γ gid pm -∗
    txnsys_inv γ p -∗
    ([∗ map] key ↦ tpl ∈ tpls, key_inv_xcmted_no_repl_tsprep γ key tpl.1 tpl.2 ts) ∗
    txnprep_auth γ gid pm ∗
    txnsys_inv γ p.
  Proof.
    iIntros (Hgid Hnone) "Hkeys Hst Htxn".
    iApply (big_sepM_impl_res with "Hkeys [Hst Htxn]").
    { iFrame. } (* why can't $ do the work? *)
    iIntros "!>" (k t Hkt) "Hkey [Hst Htxn]".
    apply elem_of_dom_2 in Hkt.
    specialize (Hgid _ Hkt). simpl in Hgid.
    rewrite /key_inv_xcmted_no_repl_tsprep.
    iDestruct (key_inv_no_repl_tsprep_unseal_kmodc with "Hkey") as (kmodc) "Hkey".
    iDestruct (key_inv_not_committed with "Hst Htxn Hkey") as %Hprep; first done.
    { apply Hnone. }
    iFrame "∗ %".
  Qed.

  Lemma key_inv_learn_prepare {γ gid ts wrs tpls} k x y :
    validate ts wrs tpls = true ->
    tpls_group gid tpls !! k = Some x ->
    tpls_group gid (acquire ts wrs tpls) !! k = Some y ->
    key_inv_xcmted_no_repl_tsprep γ k x.1 x.2 ts -∗
    key_inv_xcmted_no_repl_tsprep γ k y.1 y.2 ts.
  Proof.
    iIntros (Hvd Hx Hy) "Hkeys".
    iNamed "Hkeys". iNamed "Hkey". iNamed "Hprop".
    iFrame "∗ # %".
    iPureIntro.
    apply map_lookup_filter_Some_1_1 in Hx, Hy.
    destruct (wrs !! k) as [t | ] eqn:Hwrsk; last first.
    { (* Case: tuple not modified. *)
      rewrite acquire_unmodified in Hy; last done.
      rewrite Hy in Hx.
      by inversion Hx.
    }
    (* Case: tuple modified. *)
    assert (Hsome : is_Some (wrs !! k)) by done.
    destruct (validate_true_exists _ Hsome Hvd) as ([hist tsprep] & Hht & [Hz Hlen]).
    simpl in Hz. subst tsprep.
    rewrite Hx in Hht. inversion Hht. subst x. clear Hht.
    rewrite (acquire_modified Hsome Hx) /= in Hy.
    inversion Hy. subst y. clear Hy.
    simpl. simpl in Hdiffc.
    by apply ext_by_cmtd_inv_learn_prepare.
  Qed.

  Lemma keys_inv_learn_prepare {γ gid ts wrs tpls} :
    validate ts wrs tpls = true ->
    ([∗ map] key ↦ tpl ∈ tpls_group gid tpls,
       key_inv_xcmted_no_repl_tsprep γ key tpl.1 tpl.2 ts) -∗
    ([∗ map] key ↦ tpl ∈ tpls_group gid (acquire ts wrs tpls),
       key_inv_xcmted_no_repl_tsprep γ key tpl.1 tpl.2 ts).
  Proof.
    iIntros (Hvd) "Hkeys".
    set tpls' := acquire _ _ _.
    assert (Hdom : dom (tpls_group gid tpls') = dom (tpls_group gid tpls)).
    { apply tpls_group_dom. by rewrite acquire_dom. }
    iDestruct (big_sepM_impl_dom_eq _ _ with "Hkeys") as "Himpl".
    { apply Hdom. }
    iApply "Himpl".
    iIntros "!>" (k x y Hx Hy) "Hkey".
    by iApply (key_inv_learn_prepare with "Hkey").
  Qed.
  
  (* TODO: make proof closer to [learn_commit]; i.e., take only the required
  tuples out rather than all tuples in the group invariants. *)
  Lemma group_inv_learn_prepare γ p gid log cpool ts pwrs :
    CmdPrep ts pwrs ∈ cpool ->
    txnsys_inv γ p -∗
    ([∗ set] key ∈ keys_all, key_inv γ key) -∗
    group_inv_no_log_with_cpool γ gid log cpool ==∗
    txnsys_inv γ p ∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    group_inv_no_log_with_cpool γ gid (log ++ [CmdPrep ts pwrs]) cpool.
  Proof.
    iIntros (Hc) "Htxn Hkeys Hgroup".
    do 2 iNamed "Hgroup".
    rewrite /group_inv_no_log_with_cpool.
    (* Frame away unused resources. *)
    iFrame "Hcpool".
    destruct (stm !! ts) eqn:Hdup.
    { (* Case: Txn [ts] has already prepared, aborted, or committed; no-op. *)
      iDestruct (txn_tokens_inv_learn_prepare_noop pwrs with "Htks") as "#Htks'"; [done | done |].
      iDestruct (hist_repl_witnesses_inv_learn (CmdPrep ts pwrs) with "Hrepls Hhists") as "#Hhists'".
      { by rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hdup. }
      iFrame "∗ # %".
      by rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hdup.
    }
    assert (Hpm : pm !! ts = None).
    { rewrite -not_elem_of_dom. rewrite -not_elem_of_dom in Hdup. set_solver. }
    (* Case: Txn [ts] has not prepared, aborted, or committed. *)
    destruct (validate ts pwrs tpls) eqn:Hvd; last first.
    { (* Case: Validation fails; abort the transaction. *)
      rewrite /group_inv_no_log_no_cpool.
      rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hdup Hvd.
      (* Mark [ts] unprepared in the prepare map. *)
      iMod (txnprep_insert ts false with "Hpm") as "Hpm"; first done.
      iDestruct (txnprep_witness with "Hpm") as "#Hunp".
      { apply lookup_insert_eq. }
      iDestruct (big_sepS_elem_of with "Hvc") as "Hprep".
      { apply Hc. }
      iDestruct "Hprep" as (wrs) "(Hwrs & %Hnz & %Hpwrs)".
      (* Obtain evidence that [ts] has aborted. *)
      iMod (txnsys_inv_learn_prepare_failed with "[Hwrs Hunp] Htxn") as "[Htxn #Habt]".
      { iFrame "#". iPureIntro.
        destruct Hpwrs as (_ & Hne & Hgid).
        by eapply wrs_group_elem_of_ptgroups.
      }
      (* Create txn tokens for the new state. *)
      iDestruct (txn_tokens_inv_learn_prepare_aborted with "Habt Htks") as "#Htks'"; [done | done |].
      (* Create witnesses for the replicated history. *)
      iDestruct (hist_repl_witnesses_inv_learn (CmdPrep ts pwrs) with "Hrepls Hhists") as "#Hhists'".
      { by rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hdup Hvd. }
      (* Re-establish [valid_prepared]. *)
      iDestruct (big_sepM_insert_2 _ _ ts StAborted with "[] Hvp") as "Hvp'"; first done.
      iFrame "∗ # %".
      by auto with set_solver.
    }
    (* Case: Validation succeeds; lock the tuples and mark the transaction prepared. *)
    rewrite /group_inv_no_log_no_cpool.
    rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hdup Hvd.
    (* Extract keys invariant in this group. *)
    iDestruct (keys_inv_group gid with "Hkeys") as "[Hkeys Hkeyso]".
    (* Expose the replicated history and prepared timestamp from keys invariant. *)
    iDestruct (keys_inv_extract_repl_tsprep with "Hkeys") as (tplsK) "(Hkeys & Htpls & %Hdom)".
    (* Agree on tuples from the group and keys invariants. *)
    iDestruct (tuple_repl_big_agree with "Hrepls Htpls") as %->.
    { pose proof (apply_cmds_dom log _ _ Hrsm) as Hdom'.
      by rewrite Hdom tpls_group_keys_group_dom Hdom'.
    }
    (* Update the tuples (setting the prepared timestamp to [ts]). *)
    set tpls' := acquire _ _ _.
    iMod (tuple_repl_big_update (tpls_group gid tpls') with "Hrepls Htpls") as "[Hrepls Htpls]".
    { apply tpls_group_dom. by rewrite acquire_dom. }
    { intros k tpl1 tpl2 Htpl1 Htpl2.
      apply map_lookup_filter_Some in Htpl1 as [Htpl1 _].
      apply map_lookup_filter_Some in Htpl2 as [Htpl2 _].
      subst tpls'.
      destruct (pwrs !! k) as [v |] eqn:Hv.
      { unshelve erewrite (acquire_modified _ Htpl1) in Htpl2; first done.
        by inv Htpl2.
      }
      { rewrite (acquire_unmodified Hv) Htpl1 in Htpl2. by inv Htpl2. }
    }
    subst tpls'.
    (* Prove txn [ts] has not committed on [tpls]. *)
    iDestruct (keys_inv_not_committed with "Hkeys Hpm Htxn") as "(Hkeys & Hpm & Htxn)".
    { intros k Hk. by eapply key_to_group_tpls_group. }
    { apply Hpm. }
    (* Re-establish keys invariant w.r.t. updated tuples. *)
    iDestruct (keys_inv_learn_prepare with "Hkeys") as "Hkeys"; first done.
    (* Put ownership of tuples back to keys invariant. *)
    iDestruct (keys_inv_merge_repl_tsprep (keys_group gid keys_all) with "[Hkeys] Htpls") as "Hkeys".
    { rewrite tpls_group_keys_group_dom in Hdom.
      by rewrite tpls_group_keys_group_dom acquire_dom.
    }
    { iApply (big_sepM_mono with "Hkeys").
      iIntros (k t Hkt) "Hkey".
      iNamed "Hkey". iNamed "Hkey". iFrame "∗ #".
    }
    (* Merge the keys invariants of this group and other groups. *)
    iDestruct (keys_inv_ungroup with "Hkeys Hkeyso") as "Hkeys".
    (* Mark [ts] as prepared in the prepare map. *)
    iMod (txnprep_insert ts true with "Hpm") as "Hpm"; first done.
    (* Extract witness that [ts] has prepared. *)
    iDestruct (txnprep_witness with "Hpm") as "#Hprep".
    { apply lookup_insert_eq. }
    (* Create txn tokens for the new state. *)
    iDestruct (txn_tokens_inv_learn_prepare_prepared with "Hprep Htks") as "#Htks'"; [done | done |].
    (* Create witnesses for the replicated history. *)
    iDestruct (hist_repl_witnesses_inv_learn (CmdPrep ts pwrs) with "Hrepls Hhists") as "#Hhists'".
    { by rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hdup Hvd. }
    (* Re-establish [valid_prepared]. *)
    iDestruct (big_sepM_insert_2 _ _ ts (StPrepared pwrs) with "[] Hvp") as "Hvp'".
    { by iDestruct (big_sepS_elem_of with "Hvc") as "Hc"; first apply Hc. }
    iFrame "∗ # %".
    by auto with set_solver.
  Qed.

End inv.
