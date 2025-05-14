From Perennial.program_proof.tulip Require Import prelude.

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

Lemma no_commit_head_commit future ts wrs :
  no_commit_abort future ts ->
  head_commit future ts wrs ->
  False.
Proof.
  intros [_ Hnc] Hhc.
  specialize (Hnc wrs).
  by apply head_Some_elem_of in Hhc.
Qed.

Lemma first_abort_head_commit future ts wrs :
  first_abort future ts ->
  head_commit future ts wrs ->
  False.
Proof.
  intros (lp & ls & (Happ & [_ Hnc] & Hhead)) Hhc.
  destruct (decide (lp = [])) as [-> | Hnnil].
  { rewrite Happ /= /head_commit Hhead in Hhc. by inv Hhc. }
  assert (Hlp : ActCommit ts wrs ∈ lp).
  { apply head_Some_elem_of.
    rewrite (head_prefix _ future); [done | apply Hnnil |].
    rewrite Happ.
    by apply prefix_app_r.
  }
  by specialize (Hnc _ Hlp).
Qed.

Lemma first_commit_head_commit future lp ls ts wrs wrshd :
  first_commit future lp ls ts wrs ->
  head_commit future ts wrshd ->
  wrshd = wrs.
Proof.
  intros (Happ & [_ Hnc] & Hhead) Hhc.
  destruct lp as [| x l]; last first.
  { rewrite Happ /head_commit /= in Hhc.
    inv Hhc.
    specialize (Hnc wrshd).
    set_solver.
  }
  rewrite Happ /= /head_commit Hhead in Hhc.
  by inv Hhc.
Qed.

Lemma first_commit_compatible_head_commit future ts tshd wrs wrshd :
  first_commit_compatible future ts wrs ->
  head_commit future tshd wrshd ->
  dom wrs ∩ dom wrshd ≠ ∅ ->
  (tshd ≤ ts)%nat.
Proof.
  intros (lp & ls & (Happ & _ & Hhead) & Hcomp) Hhc Hnempty.
  destruct (decide (lp = [])) as [-> | Hnnil].
  { rewrite Happ /= /head_commit Hhead in Hhc. by inv Hhc. }
  assert (Hlp : ActCommit tshd wrshd ∈ lp).
  { apply head_Some_elem_of.
    rewrite (head_prefix _ future); [done | apply Hnnil |].
    rewrite Happ.
    by apply prefix_app_r.
  }
  rewrite /compatible_all Forall_forall in Hcomp.
  specialize (Hcomp _ Hlp).
  destruct Hcomp; [lia | contradiction].
Qed.

Lemma first_commit_incompatible_head_commit past future ts wrs wrshd :
  first_commit_incompatible past future ts wrs ->
  head_commit future ts wrshd ->
  wrshd = wrs ∧ ∃ a, a ∈ past ∧ not (compatible ts wrs a).
Proof.
  intros (lp & ls & (Happ & [_ Hnc] & Hhead) & Hincomp) Hhc.
  destruct lp as [| x l]; last first.
  { rewrite Happ /head_commit /= in Hhc.
    inv Hhc.
    specialize (Hnc wrshd).
    set_solver.
  }
  rewrite Happ /= /head_commit Hhead in Hhc.
  inv Hhc.
  split; first done.
  by rewrite app_nil_r /incompatible_exists Exists_exists in Hincomp.
Qed.

Lemma first_abort_inv_commit future ts tshd wrshd :
  head_commit future tshd wrshd ->
  first_abort future ts ->
  first_abort (tail future) ts.
Proof.
  intros Hhead Hfa.
  by unshelve eapply (first_abort_inv_tail_future _ _ _ _ Hhead Hfa).
Qed.

Lemma first_commit_compatible_inv_commit future ts tshd wrs wrshd :
  ts ≠ tshd ->
  head_commit future tshd wrshd ->
  first_commit_compatible future ts wrs ->
  first_commit_compatible (tail future) ts wrs.
Proof.
  intros Hne Hhead Hfci.
  unshelve eapply (first_commit_compatible_inv_tail_future _ _ _ _ _ Hhead).
  { intros Heq. inv Heq. }
  done.
Qed.

Lemma first_commit_incompatible_inv_commit past future ts tshd wrs wrshd :
  ts ≠ tshd ->
  head_commit future tshd wrshd ->
  first_commit_incompatible past future ts wrs ->
  first_commit_incompatible (past ++ [ActCommit tshd wrshd]) (tail future) ts wrs.
Proof.
  intros Hne Hhead Hfci.
  apply first_commit_incompatible_inv_snoc_past_tail_future.
  { intros Heq. inv Heq. }
  { done. }
  done.
Qed.

Lemma conflict_free_head_commit_eq future tmods ts wrs wrshd :
  conflict_free future tmods ->
  head_commit future ts wrshd ->
  tmods !! ts = Some wrs ->
  wrshd = wrs.
Proof.
  intros Hcf Hhead Hwrs.
  specialize (Hcf _ _ Hwrs). simpl in Hcf.
  destruct Hcf as (lp & ls & Hfc & _).
  by eapply first_commit_head_commit.
Qed.

Lemma conflict_free_head_commit_le_all future tmodcs ts wrs :
  conflict_free future tmodcs ->
  head_commit future ts wrs ->
  set_Forall (λ k, le_all ts (dom (vslice tmodcs k))) (dom wrs).
Proof.
  intros Hcf Hhead k Hk tsx Htsx.
  rewrite elem_of_dom in Htsx.
  destruct Htsx as [v Hv].
  rewrite lookup_vslice /dual_lookup in Hv.
  destruct (tmodcs !! tsx) as [wrsx |] eqn:Hwrsx; rewrite Hwrsx in Hv; last done.
  specialize (Hcf _ _ Hwrsx). simpl in Hcf.
  eapply first_commit_compatible_head_commit; [done | done |].
  apply elem_of_dom_2 in Hv.
  set_solver.
Qed.

Lemma conflict_free_inv_commit_committed ts wrs future tmodcs :
  tmodcs !! ts = None ->
  head_commit future ts wrs ->
  conflict_free future tmodcs ->
  conflict_free (tail future) tmodcs.
Proof.
  intros Hnone Hhead Hcf.
  intros tsx wrsx Hlookup.
  specialize (Hcf _ _ Hlookup). simpl in Hcf.
  eapply first_commit_compatible_inv_commit; [| apply Hhead | apply Hcf].
  intros Heq. subst tsx.
  by rewrite Hnone in Hlookup.
Qed.

Lemma conflict_free_inv_commit ts wrs future tmodcs :
  head_commit future ts wrs ->
  conflict_free future tmodcs ->
  conflict_free (tail future) (delete ts tmodcs).
Proof.
  intros Hhead Hcf.
  intros tsx wrsx Hlookup.
  rewrite lookup_delete_Some in Hlookup.
  destruct Hlookup as [Hne Hlookup].
  specialize (Hcf _ _ Hlookup). simpl in Hcf.
  eapply first_commit_compatible_inv_commit; [done | apply Hhead | apply Hcf].
Qed.

Lemma conflict_past_inv_commit ts wrs past future tmodas :
  ts ∉ dom tmodas ->
  head_commit future ts wrs ->
  conflict_past past future tmodas ->
  conflict_past (past ++ [ActCommit ts wrs]) (tail future) tmodas.
Proof.
  intros Hnoin Hhead Hcp.
  intros tsx form Hlookup.
  specialize (Hcp _ _ Hlookup). simpl in Hcp.
  apply elem_of_dom_2 in Hlookup.
  assert (Hne : ts ≠ tsx) by set_solver.
  rewrite /conflict_cases in Hcp.
  destruct form as [| | wrsx | wrsx]; simpl.
  - by apply no_commit_abort_inv_tail_future.
  - by eapply first_abort_inv_commit.
  - by apply first_commit_incompatible_inv_commit.
  - by eapply first_commit_compatible_inv_commit.
Qed.

Lemma cmtxn_in_past_inv_commit past resm ts wrs :
  cmtxn_in_past past resm ->
  cmtxn_in_past (past ++ [ActCommit ts wrs]) (<[ts := ResCommitted wrs]> resm).
Proof.
  intros Hcmtxn t m Htm.
  rewrite resm_to_tmods_insert_committed in Htm.
  destruct (decide (ts = t)) as [-> | Hne].
  { rewrite lookup_insert in Htm. inv Htm. set_solver. }
  rewrite lookup_insert_ne in Htm; last done.
  specialize (Hcmtxn _ _ Htm).
  set_solver.
Qed.

Lemma cmtxn_in_past_inv_commit_committed past resm ts wrs :
  resm !! ts = Some (ResCommitted wrs) ->
  cmtxn_in_past past resm ->
  cmtxn_in_past (past ++ [ActCommit ts wrs]) resm.
Proof.
  intros Hsome Hcmtxn t m Htm.
  specialize (Hcmtxn _ _ Htm).
  set_solver.
Qed.

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
  repl ≠ [] ->
  kmodc !! ts = None ->
  ext_by_cmtd repl cmtd kmodc ts ->
  ext_by_cmtd repl (last_extend ts cmtd ++ [v]) (<[ts := v]> kmodc) ts.
Proof.
  intros Hnz Hnnil Hts Hext.
  rewrite /ext_by_cmtd Hts in Hext.
  destruct Hext as (rts & -> & Hlen).
  rewrite /ext_by_cmtd lookup_insert.
  specialize (Hlen Hnz).
  rewrite last_extend_twice.
  assert (Hge : (rts ≤ ts)%nat).
  { etrans; last apply Hlen.
    by apply last_extend_length_ge_n.
  }
  split.
  { do 2 f_equal. lia. }
  { etrans; last apply Hlen. apply last_extend_length_ge. }
Qed.

Lemma cmtd_yield_from_kmodc_inv_commit cmtd kmodc ts v :
  (length cmtd ≤ ts)%nat ->
  cmtd ≠ [] ->
  gt_all (length cmtd) (dom kmodc) ->
  cmtd_yield_from_kmodc cmtd kmodc ->
  cmtd_yield_from_kmodc (last_extend ts cmtd ++ [v]) (<[ts:=v]> kmodc).
Proof.
  intros Hts Hnnil Hgtall Hyield t Ht.
  pose proof (last_extend_length_eq_n _ _ Hnnil Hts) as Hlen.
  destruct (decide (t < ts)%nat) as [Hlt | Hge].
  { (* Case: before write-extension [t < ts]. *)
    rewrite prev_dbval_insert; last first.
    { intros x Hx.
      specialize (Hgtall _ Hx). simpl in Hgtall.
      clear -Hts Hgtall. lia.
    }
    { apply Hlt. }
    rewrite lookup_app_l; last first.
    { clear -Hlen Hlt. lia. }
    destruct (decide (t < length cmtd)%nat) as [Hltc | Hge].
    { (* Case: before extension [t < length cmtd]. *)
      specialize (Hyield _ Hltc).
      rewrite lookup_last_extend_l; last apply Hltc.
      by rewrite Hyield.
    }
    (* Case: read-extension [length cmtd ≤ t < ts]. *)
    rewrite Nat.nlt_ge in Hge.
    rewrite lookup_last_extend_r; last first.
    { apply Hlt. }
    { clear -Hge. lia. }
    rewrite last_lookup Hyield; last first.
    { apply length_not_nil in Hnnil. clear -Hnnil. lia. }
    f_equal.
    symmetry.
    apply prev_dbval_ge.
    { clear -Hge. lia. }
    intros x Hx.
    specialize (Hgtall _ Hx). simpl in Hgtall.
    lia.
  }
  (* Case: write-extension [t = ts]. *)
  rewrite Nat.nlt_ge in Hge.
  assert (Heq : t = length (last_extend ts cmtd)).
  { rewrite length_app Hlen /= in Ht.
    rewrite Hlen.
    clear -Hge Ht. lia.
  }
  rewrite Heq lookup_snoc_length.
  f_equal. symmetry.
  apply prev_dbval_lookup.
  by rewrite Hlen lookup_insert.
Qed.

Section inv.
  Context `{!tulip_ghostG Σ}.

  Lemma keys_inv_prepared_at_ts γ resm wrs ts :
    resm !! ts = None ->
    all_prepared γ ts wrs -∗
    ([∗ set] key ∈ dom wrs, key_inv γ key) -∗
    own_txn_resm γ resm -∗
    ([∗ set] gid ∈ gids_all, group_inv γ gid) -∗
    ([∗ set] key ∈ dom wrs, key_inv_with_tsprep γ key ts) ∗
    own_txn_resm γ resm ∗
    ([∗ set] gid ∈ gids_all, group_inv γ gid).
  Proof.
    iIntros (Hnone) "#Hpreps Hkeys Hresm Hgroups".
    iApply (big_sepS_impl_res with "Hkeys [Hresm Hgroups]").
    { iFrame. }
    iIntros (k Hk) "!> Hkey [Hresm Hgroups]".
    iDestruct "Hpreps" as "[Hwrs Hpreps]".
    set gid := key_to_group k.
    iDestruct (big_sepS_elem_of _ _ gid with "Hpreps") as "Hprep".
    { by apply elem_of_key_to_group_ptgroups. }
    iDestruct (big_sepS_elem_of_acc _ _ gid with "Hgroups") as "[Hgroup HgroupsC]".
    { apply elem_of_key_to_group. }
    do 2 iNamed "Hgroup".
    iDestruct (group_prep_lookup with "Hpm Hprep") as %Hp.
    assert (is_Some (stm !! ts)) as [res Hres].
    { rewrite -elem_of_dom. by specialize (Hpmstm _ _ Hp). }
    destruct res as [pwrs | |]; last first.
    { (* Case: Txn [ts] has already aborted. Contradiction. *)
      iDestruct (big_sepM_lookup with "Hsafestm") as "Habt"; first apply Hres.
      iDestruct (txn_res_lookup with "Hresm Habt") as %Habt.
      congruence.
    }
    { (* Case: Txn [ts] has already committed. Contradiction. *)
      iDestruct (big_sepM_lookup with "Hsafestm") as "Hcmt"; first apply Hres.
      iDestruct "Hcmt" as (wrs') "Hcmt".
      iDestruct (txn_res_lookup with "Hresm Hcmt") as %Hcmt.
      congruence.
    }
    iDestruct (big_sepM_lookup with "Hsafestm") as "Hpreped"; first apply Hres.
    iDestruct "Hpreped" as "[Hpreped Hsafep]".
    iDestruct "Hsafep" as (wrs') "(Hwrs' & _ & %Hvw & %Hne & %Hpwrs)".
    iDestruct (txn_wrs_agree with "Hwrs Hwrs'") as %->.
    assert (Hinpwrs : k ∈ dom pwrs).
    { rewrite Hpwrs /wrs_group.
      assert (Hgoal : k ∈ filter (λ k, key_to_group k = gid) (dom wrs)).
      { by rewrite elem_of_filter. }
      by rewrite filter_dom_L in Hgoal.
    }
    (* From [prepared_impl_locked] we know [k] is locked by [ts]. *)
    pose proof (Hpil _ _ _ Hres Hinpwrs) as Hlocked.
    (* Take [tuple_repl_half] from [Hrepls]. *)
    iDestruct (big_sepM_lookup_acc _ _ k ts with "Hlocks") as "[Hlock HlocksC]".
    { by rewrite /tpls_group map_lookup_filter_Some. }
    iDestruct (key_inv_expose_tsprep with "Hkey") as (tsprep) "Hkey".
    (* Finally, deduce [tsprep = ts]. *)
    iAssert (⌜tsprep = ts⌝)%I as %->.
    { do 2 iNamed "Hkey".
      by iDestruct (repl_ts_agree with "Htsprep Hlock") as %?.
    }
    iDestruct ("HlocksC" with "Hlock") as "Hlocks".
    iDestruct ("HgroupsC" with "[-Hresm Hkey]") as "Hgroups".
    { iFrame "∗ # %". }
    iFrame.
  Qed.

  Definition key_inv_after_commit
    γ (key : dbkey) (tsprep : nat) (kmodl kmodc : dbkmod) : iProp Σ :=
    ∃ v, let kmodl' := delete tsprep kmodl in
         let kmodc' := <[tsprep := v]> kmodc in
         key_inv_with_tsprep_no_kmodl_no_kmodc γ key tsprep kmodl' kmodc' ∗
         ⌜kmodl !! tsprep = Some v⌝.

  Lemma key_inv_commit γ kmodl kmodc ts k v :
    ts ≠ O ->
    le_all ts (dom kmodl) ->
    kmodl !! ts = Some v ->
    kmodc !! ts = None ->
    quorum_validated_key γ k ts -∗
    key_inv_with_tsprep_no_kmodl_no_kmodc γ k ts kmodl kmodc ==∗
    key_inv_with_tsprep_no_kmodl_no_kmodc γ k ts (delete ts kmodl) (<[ts:=v]> kmodc) ∗
    is_cmtd_hist_length_lb γ k (S ts).
  Proof.
    iIntros (Hnz Hles Hkmodl Hkmodc) "#Hqv Hkey".
    do 2 iNamed "Hkey".
    pose proof (ext_by_lnrz_impl_cmtd_not_nil _ _ _ Hdiffl) as Hnnil.
    pose proof (ext_by_cmtd_length_cmtd _ _ _ _ Hnz Hkmodc Hdiffc) as Hlenc.
    pose proof (ext_by_lnrz_inv_commit _ _ _ _ _ Hkmodl Hles Hdiffl) as Hdiffl'.
    unshelve epose proof (ext_by_cmtd_inv_commit _ _ _ _ v Hnz _ Hkmodc Hdiffc) as Hdiffc'.
    { eapply ext_by_cmtd_partial_impl_repl_not_nil; [| apply Hkmodc | apply Hdiffc].
      by eapply ext_by_lnrz_impl_cmtd_not_nil.
    }
    set cmtd' := last_extend _ _ ++ _ in Hdiffl'.
    iMod (cmtd_hist_update cmtd' with "Hcmtd") as "Hcmtd".
    { apply prefix_app_r, last_extend_prefix. }
    iDestruct (cmtd_hist_witness with "Hcmtd") as "#Hlb".
    iModIntro.
    unshelve epose proof (last_extend_length_eq_n ts cmtd _ _) as Hlen.
    { apply Hnnil. }
    { apply Hlenc. }
    iSplit; last first.
    { iFrame "Hlb".
      iPureIntro.
      rewrite length_app Hlen /=.
      lia.
    }
    iFrame "∗ # %".
    iSplit.
    { rewrite length_app Hlen Nat.add_1_r.
      iDestruct "Hqv" as (ridsq) "[Hqv %Hridsq]".
      iExists ridsq.
      iSplit; last done.
      iApply (big_sepS_mono with "Hqv").
      iIntros (rid _) "Hrv".
      iApply (replica_key_validation_at_length with "Hrv").
    }
    iSplit.
    { rewrite {2}/committed_or_quorum_invalidated_key length_app Hlen /=.
      by rewrite Nat.add_1_r /= lookup_insert.
    }
    iSplit.
    { iApply (big_sepM_insert_2 with "[] Hqvk"). iFrame "Hqv". }
    iPureIntro.
    split.
    { intros x Hx.
      rewrite dom_insert_L elem_of_union elem_of_singleton in Hx.
      destruct Hx as [Hx | Hx]; last first.
      { specialize (Hltlenc _ Hx). simpl in Hltlenc.
        etrans; first apply Hltlenc.
        rewrite length_app /=.
        clear -Hlenc Hlen. lia.
      }
      subst x.
      rewrite length_app /= Hlen.
      lia.
    }
    split.
    { apply cmtd_yield_from_kmodc_inv_commit.
      { apply Hlenc. }
      { apply Hnnil. }
      { apply Hltlenc. }
      { apply Hyield. }
    }
    { by rewrite lookup_insert_ne. }
  Qed.

  Lemma keys_inv_commit γ kmodls kmodcs ts :
    ts ≠ O ->
    map_Forall (λ _ kmodl, le_all ts (dom kmodl)) kmodls ->
    map_Forall (λ _ kmodl, is_Some (kmodl !! ts)) kmodls ->
    map_Forall (λ _ kmodc, kmodc !! ts = None) kmodcs ->
    ([∗ set] k ∈ dom kmodls, quorum_validated_key γ k ts) -∗
    ([∗ map] key ↦ kmodl;kmodc ∈ kmodls;kmodcs,
       key_inv_with_tsprep_no_kmodl_no_kmodc γ key ts kmodl kmodc) ==∗
    ([∗ map] key ↦ kmodl;kmodc ∈ kmodls;kmodcs,
       key_inv_after_commit γ key ts kmodl kmodc ∗ is_cmtd_hist_length_lb γ key (S ts)).
  Proof.
    iIntros (Hnz Hles Hkmodls Hkmodcs) "#Hqv Hkeys".
    iApply big_sepM2_bupd.
    iApply (big_sepM2_impl with "Hkeys").
    iIntros (k kmodl kmodc Hkmodl Hkmodc) "!> Hkey".
    specialize (Hkmodls _ _ Hkmodl). simpl in Hkmodls.
    specialize (Hles _ _ Hkmodl). simpl in Hles.
    specialize (Hkmodcs _ _ Hkmodc). simpl in Hkmodcs.
    destruct Hkmodls as [v Hv].
    apply elem_of_dom_2 in Hkmodl.
    iDestruct (big_sepS_elem_of with "Hqv") as "Hkqv"; first apply Hkmodl.
    iMod (key_inv_commit with "Hkqv Hkey") as "[Hkey #Hlb]"; try done.
    iModIntro.
    iSplit; last iFrame "Hlb".
    iExists v.
    by iFrame "%".
  Qed.

  Lemma partitioned_tids_close {γ} tids tmodcs tmodas resm :
    let wcmts := dom tmodcs in
    let wabts := dom tmodas in
    let cmts := dom (resm_to_tmods resm) in
    set_Forall (λ tid : nat, tid ∈ dom resm ∨ tid ∈ wabts ∨ tid ∈ wcmts) tids ->
    ([∗ set] tid ∈ wcmts, own_excl_tid γ tid) -∗
    ([∗ set] tid ∈ wabts, own_excl_tid γ tid) -∗
    ([∗ set] tid ∈ cmts, own_excl_tid γ tid) -∗
    partitioned_tids γ tids tmodcs tmodas resm.
  Proof. iIntros (wcmts wabts cmts Hfate) "Hwcmts Habts Hcmts". iFrame "∗ %". Qed.

  Lemma txnsys_inv_commit γ tid wrs future :
    head_commit future tid wrs ->
    is_lnrz_tid γ tid -∗
    all_prepared γ tid wrs -∗
    txnsys_inv_no_future γ future -∗
    ([∗ set] gid ∈ gids_all, group_inv γ gid) -∗
    ([∗ set] gid ∈ gids_all, ([∗ set] rid ∈ rids_all, replica_inv γ gid rid)) -∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ==∗
    txnsys_inv_no_future γ (tail future) ∗
    ([∗ set] gid ∈ gids_all, group_inv γ gid) ∗
    ([∗ set] gid ∈ gids_all, ([∗ set] rid ∈ rids_all, replica_inv γ gid rid)) ∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    is_txn_committed γ tid wrs.
  Proof.
    iIntros (Hhead) "#Htid #Hprep Htxnsys Hgroups Hrps Hkeys".
    do 2 iNamed "Htxnsys".
    iDestruct (lnrz_tid_elem_of with "Htxnsl Htid") as %Htid.
    iNamed "Hpart".
    apply Hfate in Htid as Hcases.
    destruct Hcases as [Hinresm | Hcases].
    { (* Case: Txn [tid] has already aborted or committed. *)
      apply elem_of_dom in Hinresm as [res Hres].
      destruct res as [wrsc |]; last first.
      { (* Case: Txn [tid] has already aborted. Contradiction. *)
        iDestruct (big_sepM_lookup with "Hvr") as "#Hvabt"; first apply Hres.
        iDestruct (all_prepared_valid_res_aborted with "Hprep Hvabt") as %[].
      }
      iDestruct (big_sepM_lookup with "Hvr") as "#Hres"; first apply Hres.
      iAssert (⌜wrsc = wrs⌝)%I as %->.
      { iDestruct "Hres" as "[Hwrsc _]".
        iDestruct "Hprep" as "[Hwrs _]".
        by iDestruct (txn_wrs_agree with "Hwrs Hwrsc") as %?.
      }
      (* Case: Txn [tid] has already committed. Extract a witness without any update. *)
      iDestruct (txn_res_witness with "Hresm") as "#Hcmt"; first apply Hres.
      (* Obtain [tid ∉ dom tmodcs] and [tid ∉ dom tmodas]. *)
      apply lookup_resm_to_tmods_Some in Hres as Hwrs.
      apply elem_of_dom_2 in Hwrs as Hincmt.
      iDestruct (big_sepS_elem_of_acc with "Hcmts") as "[Htidexcl HcmtsC]"; first apply Hincmt.
      iDestruct (excl_tid_not_elem_of with "Hwcmts Htidexcl") as %Hnotinc.
      iDestruct (excl_tid_not_elem_of with "Hwabts Htidexcl") as %Hnotina.
      iDestruct ("HcmtsC" with "Htidexcl") as "Hcmts".
      pose proof (Hcmtxn _ _ Hwrs) as Hinpast. simpl in Hinpast.
      iDestruct (big_sepL_elem_of with "Hpas") as "Hpawitness"; first apply Hinpast.
      iCombine "Hpas Hpawitness" as "Hpas'".
      rewrite -big_sepL_snoc.
      unshelve epose proof (conflict_free_inv_commit_committed _ _ _ _ _ Hhead Hcf) as Hcf'.
      { apply not_elem_of_dom_1, Hnotinc. }
      unshelve epose proof (conflict_past_inv_commit _ _ _ _ _ Hnotina Hhead Hcp) as Hcp'.
      iDestruct (partitioned_tids_close with "Hwcmts Hwabts Hcmts") as "Hpart".
      { apply Hfate. }
      pose proof (cmtxn_in_past_inv_commit_committed _ _ _ _ Hres Hcmtxn) as Hcmtxn'.
      by iFrame "∗ # %".
    }
    destruct Hcases as [Htmodas | Htmodcs].
    { (* Case: Txn [tid] predicted to abort. Contradiction. *)
      apply elem_of_dom in Htmodas as Hform.
      destruct Hform as [form Hform].
      specialize (Hcp _ _ Hform). simpl in Hcp.
      rewrite /conflict_cases in Hcp.
      destruct form as [| | wrsa | wrsa].
      { (* Case NCA: [tid] not showing at all in [future] -> contradicting [Hhead]. *)
        destruct (no_commit_head_commit _ _ _ Hcp Hhead) as [].
      }
      { (* Case FA: first commit/abort action is abort -> contradicting [Hhead]. *)
        destruct (first_abort_head_commit _ _ _ Hcp Hhead) as [].
      }
      { (* Case FCI: [(tid, wrs)] conflicting with prior action. *)
        (* Obtain [resm !! ts = None]. *)
        iDestruct (big_sepS_delete with "Hwabts") as "[Htidexcl Hwabts]"; first apply Htmodas.
        iDestruct (excl_tid_not_elem_of with "Hcmts Htidexcl") as %Hnotinr.
        rewrite not_elem_of_dom lookup_resm_to_tmods_None in Hnotinr.
        destruct Hnotinr as [Hnone | Habt]; last first.
        { iDestruct (big_sepM_lookup with "Hvr") as "Habt"; first apply Habt.
          iDestruct (all_prepared_valid_res_aborted with "Hprep Habt") as %[].
        }
        (* Obtain [wrsa = wrs] and and incompatible action [a ∈ past]. *)
        pose proof (first_commit_incompatible_head_commit _ _ _ _ _ Hcp Hhead) as [Heq Hic].
        subst wrsa.
        destruct Hic as (a & Hinpast & Hic).
        (* Take [dom wrs] of [key_inv] and obtain [tid ≠ O]. *)
        iAssert (⌜dom wrs ⊆ keys_all ∧ tid ≠ O⌝)%I as %[Hdom Htidnz].
        { iDestruct "Hprep" as "[Hwrs _]".
          iDestruct (txn_wrs_lookup with "Hwrs Hwrsm") as %Hlookup.
          apply lookup_wrsm_dbmap_Some in Hlookup.
          specialize (Hwrsm _ _ Hlookup). simpl in Hwrsm.
          destruct Hwrsm as [Hvt Hvw].
          iPureIntro.
          split; first done.
          rewrite /valid_ts in Hvt.
          lia.
        }
        iDestruct (big_sepS_subseteq _ _ (dom wrs) with "Hkeys") as "Hkeys".
        { apply Hdom. }
        (* Prove that for all [key ∈ dom wrsa], the lock must be currently granted to [tid]. *)
        iDestruct (keys_inv_prepared_at_ts with "Hprep Hkeys Hresm Hgroups")
          as "(Hkeys & Hresm & Hgroups)"; first done.
        iDestruct (big_sepL_elem_of with "Hpas") as "Ha"; first apply Hinpast.
        destruct a as [tsa wrsa | tsa | tsa keya].
        { (* Case [a = ActCommit tsa wrsa]. *)
          apply Decidable.not_or in Hic as [Hge Hne].
          apply Nat.nlt_ge in Hge.
          apply set_choose_L in Hne as [k Hk].
          rewrite elem_of_intersection in Hk.
          destruct Hk as [Hinwrs Hinwrsa].
          (* Obtain [tsa < length hlb]. *)
          simpl.
          iDestruct (big_sepS_elem_of with "Ha") as (hlb) "[Hhlb %Hlengt]"; first apply Hinwrsa.
          iDestruct (big_sepS_elem_of with "Hkeys") as "Hkey"; first apply Hinwrs.
          do 2 iNamed "Hkey".
          (* Obtain [length hlb ≤ length cmtd]. *)
          iDestruct (cmtd_hist_prefix with "Hcmtd Hhlb") as %Hprefix.
          apply prefix_length in Hprefix.
          (* Obtain [length cmtd ≤ tid]. *)
          iAssert (⌜(length cmtd ≤ tid)%nat⌝)%I as %Hlenle.
          { iDestruct (big_sepS_elem_of _ _ k with "Hkmodcs") as "Hkmodc'".
            { set_solver. }
            iDestruct (cmtd_kmod_agree with "Hkmodc Hkmodc'") as %Hkmodceq.
            iPureIntro.
            eapply ext_by_cmtd_length_cmtd; [apply Htidnz | | apply Hdiffc].
            by rewrite -Hkmodceq vslice_resm_to_tmods_not_terminated.
          }
          exfalso. clear -Hge Hlengt Hlenle Hprefix. lia.
        }
        { (* Case [a = ActAbort tsa]. *)
          by simpl in Hic.
        }
        { (* Case [a = ActRead tsa keya]. *)
          apply Decidable.not_or in Hic as [Hgt Hin].
          apply Nat.nle_gt in Hgt.
          apply dec_stable in Hin.
          (* Obtain [tsa ≤ length hlb]. *)
          iDestruct "Ha" as (hlb) "[Hhlb %Hlenge]".
          (* Obtain [length h ≤ tid]. *)
          iDestruct (big_sepS_elem_of with "Hkeys") as "Hkey"; first apply Hin.
          do 2 iNamed "Hkey".
          (* Obtain [length hlb ≤ length cmtd]. *)
          iDestruct (cmtd_hist_prefix with "Hcmtd Hhlb") as %Hprefix.
          apply prefix_length in Hprefix.
          iAssert (⌜(length cmtd ≤ tid)%nat⌝)%I as %Hlenle.
          { iDestruct (big_sepS_elem_of _ _ keya with "Hkmodcs") as "Hkmodc'".
            { set_solver. }
            iDestruct (cmtd_kmod_agree with "Hkmodc Hkmodc'") as %Hkmodceq.
            iPureIntro.
            eapply ext_by_cmtd_length_cmtd; [apply Htidnz | | apply Hdiffc].
            by rewrite -Hkmodceq vslice_resm_to_tmods_not_terminated.
          }
          exfalso. clear -Hgt Hlenge Hlenle Hprefix. lia.
        }
      }
      { (* Case FCC: [(tid, wrs)] does not satisfy [Q wrs]. *)
        (* Obtain [wrsa = wrs]. *)
        destruct Hcp as (lp & ls & Hfc & _).
        pose proof (first_commit_head_commit _ _ _ _ _ _ Hfc Hhead) as <-.
        (* Obtain [incorrect_wrs γ tid wrs]. *)
        iDestruct (big_sepM_lookup with "Hiwrs") as "Hneg"; first apply Hform.
        simpl.
        (* Obtain [correct_wrs γ tid wrs]. *)
        iDestruct "Hprep" as "[Hwrs _]".
        iDestruct (txn_wrs_lookup with "Hwrs Hwrsm") as %Hwrs.
        apply lookup_wrsm_dbmap_Some in Hwrs.
        iDestruct (big_sepM_lookup with "Hcwrs") as "Hpos"; first apply Hwrs.
        iDestruct (correct_incorrect_wrs with "Hpos Hneg") as %[].
      }
    }
    (* Case: Txn [tid] predicted to commit. Update states and extract commitment witness. *)
    (* Obtain [resm !! ts = None] and [ts ∉ dom tmodas]. *)
    iDestruct (big_sepS_delete with "Hwcmts") as "[Htidexcl Hwcmts]"; first apply Htmodcs.
    iDestruct (excl_tid_not_elem_of with "Hcmts Htidexcl") as %Hnotinr.
    iDestruct (excl_tid_not_elem_of with "Hwabts Htidexcl") as %Hnotina.
    rewrite not_elem_of_dom lookup_resm_to_tmods_None in Hnotinr.
    destruct Hnotinr as [Hnone | Habt]; last first.
    { iDestruct (big_sepM_lookup with "Hvr") as "Habt"; first apply Habt.
      iDestruct (all_prepared_valid_res_aborted with "Hprep Habt") as %[].
    }
    (* Obtain [wrsx], the write set in the result map of [tid]. *)
    rewrite elem_of_dom in Htmodcs.
    destruct Htmodcs as [wrsx Hwrs].
    (* Obtain eq of write set between the predicted [wrs] and the [wrsx] in the result map. *)
    pose proof (conflict_free_head_commit_eq _ _ _ _ _ Hcf Hhead Hwrs). subst wrsx.
    iAssert (⌜dom wrs ⊆ keys_all⌝)%I as %Hdom.
    { iDestruct "Hprep" as "[Hwrs _]".
      iDestruct (txn_wrs_lookup with "Hwrs Hwrsm") as %Hlookup.
      apply lookup_wrsm_dbmap_Some in Hlookup.
      specialize (Hwrsm _ _ Hlookup).
      by destruct Hwrsm as [_ Hgoal].
    }
    (* Take [dom wrs] of [own_lnrz_kmod_half] and [own_cmtd_kmod_half]. *)
    iDestruct (big_sepS_subseteq_difference_1 _ _ (dom wrs) with "Hkmodls") as "[Hkmodls HkmodlsO]".
    { apply Hdom. }
    iDestruct (big_sepS_subseteq_difference_1 _ _ (dom wrs) with "Hkmodcs") as "[Hkmodcs HkmodcsO]".
    { apply Hdom. }
    (* Take [dom wrs] of [key_inv]. *)
    iDestruct (big_sepS_subseteq_acc _ _ (dom wrs) with "Hkeys") as "[Hkeys HkeysC]".
    { apply Hdom. }
    (* Prove that for all [key ∈ dom wrs], the lock must be currently granted to [tid]. *)
    iDestruct (keys_inv_prepared_at_ts with "Hprep Hkeys Hresm Hgroups")
      as "(Hkeys & Hresm & Hgroups)"; [done |].
    (* Extract [own_lnrz_kmod_half] and [own_cmtd_kmod_half] out of [key_inv]. *)
    iDestruct (keys_inv_with_tsprep_extract_kmodl_kmodc with "Hkeys") as "Hkeys".
    iDestruct "Hkeys" as (kmodls kmodcs) "(Hkeys & Hkmodls' & Hkmodcs' & %Hdomkmodls)".
    iDestruct (big_sepM2_dom with "Hkeys") as %Hdomkmodcs.
    rewrite Hdomkmodls in Hdomkmodcs. symmetry in Hdomkmodcs.
    (* Agreement of [own_lnrz_kmod_half] and [own_cmtd_kmod_half] from [txnsys_inv] and [key_inv]. *)
    iDestruct (lnrz_kmod_big_agree with "Hkmodls Hkmodls'") as %Hkmodls.
    { apply Hdomkmodls. }
    iDestruct (cmtd_kmod_big_agree with "Hkmodcs Hkmodcs'") as %Hkmodcs.
    { apply Hdomkmodcs. }
    (* Agreement and update of [own_lnrz_kmod_half] and [own_cmtd_kmod_half]. *)
    set tmodcs' := delete tid tmodcs.
    iMod (lnrz_kmod_big_update (λ k, vslice tmodcs' k) with
           "Hkmodls Hkmodls'") as "[Hkmodls Hkmodls']".
    { apply Hdomkmodls. }
    iAssert ([∗ map] k ↦ kmod ∈ kmodls, own_lnrz_kmod_half γ k (delete tid kmod))%I
      with "[Hkmodls']" as "Hkmodls'".
    { iApply (big_sepM_impl with "Hkmodls'").
      iIntros (k kmod Hkmod) "!> Hkmods".
      subst tmodcs'.
      specialize (Hkmodls _ _ Hkmod).
      by rewrite vslice_delete Hkmodls.
    }
    set resm' := <[tid := ResCommitted wrs]> resm.
    iMod (cmtd_kmod_big_update (λ k, vslice (resm_to_tmods resm') k) with "Hkmodcs Hkmodcs'")
      as "[Hkmodcs Hkmodcs']".
    { apply Hdomkmodcs. }
    iAssert ([∗ map] k ↦ kmod; v ∈ kmodcs; wrs, own_cmtd_kmod_half γ k (<[tid := v]> kmod))%I
      with "[Hkmodcs']" as "Hkmodcs'".
    { iApply (big_sepM_sepM2_impl with "Hkmodcs'"); first done.
      iIntros (k kmod v Hkmod Hv) "!> Hkmods".
      specialize (Hkmodcs _ _ Hkmod).
      subst resm'.
      by rewrite resm_to_tmods_insert_committed (vslice_insert_Some _ _ _ _ _ Hv) Hkmodcs.
    }
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
    (* For each [k ∈ dom wrs], obtain that its validation has been fixed by some quorum. *)
    iAssert ([∗ set] gid ∈ ptgroups (dom wrs),
               [∗ set] key ∈ keys_group gid (dom wrs),
                 quorum_validated_key γ key tid)%I as "#Hvdlb".
    { iDestruct "Hprep" as "[Hwrs Hprep]".
      iApply big_sepS_forall.
      iIntros (gid Hgid).
      iDestruct (big_sepS_elem_of with "Hprep") as "Hpreped"; first apply Hgid.
      assert (Hinall : gid ∈ gids_all).
      { apply (elem_of_weaken _ _ _ Hgid), subseteq_ptgroups. }
      iDestruct (big_sepS_elem_of with "Hgroups") as "Hgroup"; first apply Hinall.
      do 2 iNamed "Hgroup".
      iDestruct (group_prep_lookup with "Hpm Hpreped") as %Hpreped.
      iDestruct (big_sepM_lookup with "Hsafepm") as "Hsafep"; first apply Hpreped.
      iDestruct "Hsafep" as "[_ Hqv]".
      iDestruct (big_sepS_elem_of with "Hrps") as "Hrps"; first apply Hinall.
      iDestruct "Hqv" as (ridsq) "[Hqv %Hridsq]".
      iDestruct (replicas_inv_validated_keys_of_txn with "Hqv [Hrps]") as "#Hvpwrs".
      { iApply (big_sepS_subseteq with "Hrps").
        by destruct Hridsq as [? _].
      }
      iApply big_sepS_forall.
      iIntros (k Hk).
      iExists ridsq.
      iSplit; last done.
      iApply big_sepS_forall.
      iIntros (rid Hrid).
      iDestruct (big_sepS_elem_of with "Hvpwrs") as (pwrs) "[Hpwrs Hvds]"; first apply Hrid.
      iDestruct "Hpwrs" as (wrs') "[Hwrs' %Hpwrs]".
      iDestruct (txn_wrs_agree with "Hwrs Hwrs'") as %->.
      rewrite -wrs_group_keys_group_dom -Hpwrs in Hk.
      iDestruct (big_sepS_elem_of with "Hvds") as "Hvd"; first apply Hk.
      apply elem_of_dom in Hk as [v Hv].
      rewrite Hpwrs lookup_wrs_group_Some in Hv.
      destruct Hv as [_ ->].
      iDestruct "Hvd" as (l) "[Hvd %Hlookup]".
      iFrame "Hvd %".
    }
    iDestruct (big_sepS_partition_2 with "Hvdlb") as "Hvdlb'".
    { intros k Hk.
      exists (key_to_group k).
      split; last done.
      by apply elem_of_key_to_group_ptgroups.
    }
    rewrite -Hdomkmodls.
    (* Re-establish [key_inv] w.r.t. commit. *)
    iMod (keys_inv_commit with "Hvdlb' Hkeys") as "Hkeys".
    { by eapply Hnz, elem_of_dom_2. }
    { intros k kmodl Hkmodl.
      pose proof (conflict_free_head_commit_le_all _ _ _ _ Hcf Hhead) as Hle.
      assert (Hk : k ∈ dom wrs).
      { by rewrite -Hdomkmodls elem_of_dom. }
      specialize (Hle _ Hk). simpl in Hle.
      specialize (Hkmodls _ _ Hkmodl). simpl in Hkmodls.
      by rewrite Hkmodls.
    }
    { apply Hkmodlstid. }
    { apply Hkmodcstid. }
    rewrite big_sepM2_sep.
    iDestruct "Hkeys" as "[Hkeys #Hlbs]".
    rewrite big_sepM2_alt.
    iDestruct "Hlbs" as "[_ Hlbs]".
    rewrite -big_sepS_big_sepM dom_map_zip_with_L Hdomkmodls Hdomkmodcs.
    replace (dom wrs ∩ dom wrs) with (dom wrs); last set_solver.
    iAssert ([∗ map] k ↦ kmodl;kmodc ∈ kmodls; kmodcs,
               ∃ v, own_cmtd_kmod_half γ k (<[tid := v]> kmodc) ∗ ⌜kmodl !! tid = Some v⌝)%I
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
      iApply big_sepS_big_sepM.
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
    (* Update the unmodified part of [own_lnrz_kmod_half]. *)
    iAssert ([∗ set] x ∈ (keys_all ∖ dom wrs), own_lnrz_kmod_half γ x (vslice tmodcs' x))%I
      with "[HkmodlsO]" as "HkmodlsO".
    { iApply (big_sepS_impl with "HkmodlsO").
      iIntros (k Hk) "!> Hkmod".
      subst tmodcs'.
      assert (Hnotinwrs : wrs !! k = None).
      { rewrite -not_elem_of_dom. set_solver. }
      by rewrite (vslice_delete_None _ _ _ _ Hwrs Hnotinwrs).
    }
    (* Update the unmodified part of [own_cmtd_kmod_half]. *)
    iAssert ([∗ set] x ∈ (keys_all ∖ dom wrs),
               own_cmtd_kmod_half γ x (vslice (resm_to_tmods resm') x))%I
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
    (* Combine the modified and unmodified parts of [own_lnrz_kmod_half] and [own_cmtd_kmod_half]. *)
    iDestruct (big_sepS_subseteq_difference_2 with "Hkmodls HkmodlsO") as "Hkmodls".
    { apply Hdom. }
    iDestruct (big_sepS_subseteq_difference_2 with "Hkmodcs HkmodcsO") as "Hkmodcs".
    { apply Hdom. }
    (* Add [(tid, ResCommitted wrs)] to [resm] and extract a witness. *)
    iMod (txn_res_insert _ (ResCommitted wrs) with "Hresm") as "Hresm"; first apply Hnone.
    iDestruct (txn_res_witness tid with "Hresm") as "#Hcmt".
    { by rewrite lookup_insert. }
    (* Re-establish [valid_res]. *)
    iDestruct (big_sepM_insert_2 _ _ tid (ResCommitted wrs) with "[] Hvr") as "Hvr'"; first done.
    (* Re-establish [past_action_witness]. *)
    iAssert (past_action_witness γ (ActCommit tid wrs))%I as "#Hpa"; first iFrame "Hlbs".
    iCombine "Hpas Hpa" as "Hpas'".
    rewrite -big_sepL_snoc.
    (* Re-establish [conflict_free], [conflict_past], and [cmtxn_in_past]. *)
    pose proof (conflict_free_inv_commit _ _ _ _ Hhead Hcf) as Hcf'.
    pose proof (conflict_past_inv_commit _ _ _ _ _ Hnotina Hhead Hcp) as Hcp'.
    pose proof (cmtxn_in_past_inv_commit _ _ tid wrs Hcmtxn) as Hcmtxn'.
    (* Add [tids_excl_frag γ tid] (originally from [wcmts]) to [cmts]. *)
    iDestruct (big_sepS_insert_2 with "Htidexcl Hcmts") as "Hcmts".
    iDestruct (partitioned_tids_close tids tmodcs' tmodas resm'
                with "[Hwcmts] Hwabts [Hcmts]") as "Hpart".
    { intros tidx Htidx.
      rewrite dom_insert_L.
      specialize (Hfate _ Htidx). simpl in Hfate.
      destruct Hfate as [Hcmt | Hfate].
      { left. set_solver. }
      destruct Hfate as [Hwabt | Hwcmt].
      { right. left. done. }
      destruct (decide (tidx = tid)) as [-> | Hne].
      { left. set_solver. }
      right. right. rewrite dom_delete_L. set_solver.
    }
    { by rewrite dom_delete_L. }
    { by rewrite resm_to_tmods_insert_committed dom_insert_L. }
    iFrame "∗ # %".
    iModIntro.
    iPureIntro.
    rewrite dom_delete_L.
    split; last set_solver.
    intros t m Htm.
    specialize (Htidcs _ _ Htm). simpl in Htidcs.
    subst tmodcs' resm'.
    destruct (decide (t = tid)) as [-> | Hne]; last first.
    { rewrite lookup_insert_ne; last done.
      rewrite lookup_delete_ne; last done.
      apply Htidcs.
    }
    right.
    rewrite lookup_insert.
    destruct Htidcs as [Hm | Hm].
    { rewrite Hm in Hwrs. by inv Hwrs. }
    by rewrite Hm in Hnone.
  Qed.

End inv.
