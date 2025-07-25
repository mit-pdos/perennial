From Perennial.program_proof.tulip Require Import prelude.
From Perennial.program_proof.tulip.invariance Require Import cmd.

Lemma ext_by_cmtd_inv_learn_abort {repl cmtd kmod} ts :
  kmod !! O = None ->
  kmod !! ts = None ->
  ext_by_cmtd repl cmtd kmod ts ->
  ext_by_cmtd repl cmtd kmod O.
Proof.
  intros Hz Hts Hdiff.
  rewrite /ext_by_cmtd Hts in Hdiff.
  rewrite /ext_by_cmtd Hz.
  destruct Hdiff as (rts & Hext & _).
  by exists rts.
Qed.

Section inv.
  Context `{!heapGS Σ}.
  Context `{!tulip_ghostG Σ}.

  Lemma keys_inv_prepared {γ p ts} keys :
    is_txn_aborted γ ts -∗
    ([∗ set] key ∈ keys, key_inv_no_tsprep γ key ts) -∗
    txnsys_inv γ p -∗
    ([∗ set] key ∈ keys, key_inv_prepared_no_tsprep γ key ts) ∗
    txnsys_inv γ p.
  Proof.
    iIntros "#Habt Hkeys Htxnsys".
    iApply (big_sepS_impl_res with "Hkeys Htxnsys").
    iIntros (k Hk) "!> Hkey Htxnsys".
    do 2 iNamed "Htxnsys".
    iDestruct (txn_res_lookup with "Hresm Habt") as %Hresm.
    do 2 iNamed "Hkey".
    iDestruct (cmtd_kmod_vslice_agree with "Hkmodcs Hkmodc") as %Hkmodc.
    { apply Hall. }
    assert (Hnc : kmodc !! ts = None).
    { subst kmodc. by eapply vslice_resm_to_tmods_aborted. }
    iAssert (txnsys_inv γ p)%I with "[-Hkmodl Hkmodc Hdbv Hlnrz Hcmtd Hrepl]" as "Htxnsys".
    { iFrame "∗ # %". }
    iFrame "∗ # %".
  Qed.

  Lemma key_inv_learn_abort {γ ts} k :
    key_inv_prepared_no_tsprep γ k ts -∗
    key_inv_no_tsprep γ k O.
  Proof.
    iIntros "Hkey".
    do 3 iNamed "Hkey".
    iFrame "∗ # %".
    iPureIntro.
    by apply (ext_by_cmtd_inv_learn_abort ts).
  Qed.

  Lemma keys_inv_learn_abort {γ ts keys} :
    ([∗ set] key ∈ keys, key_inv_prepared_no_tsprep γ key ts) -∗
    ([∗ set] key ∈ keys, key_inv_no_tsprep γ key O).
  Proof.
    iIntros "Hkeys".
    iApply (big_sepS_mono with "Hkeys").
    iIntros (k Hk) "Hkey".
    iApply (key_inv_learn_abort with "Hkey").
  Qed.

  Lemma group_inv_learn_abort γ p gid log cpool ts :
    txn_cpool_subsume_log cpool (log ++ [CmdAbort ts]) ->
    txnsys_inv γ p -∗
    ([∗ set] key ∈ keys_all, key_inv γ key) -∗
    group_inv_no_log_with_cpool γ gid log cpool ==∗
    txnsys_inv γ p ∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    group_inv_no_log_with_cpool γ gid (log ++ [CmdAbort ts]) cpool.
  Proof.
    iIntros (Hsubsume) "Htxnsys Hkeys Hgroup".
    pose proof Hsubsume as Hcscincl.
    rewrite /txn_cpool_subsume_log Forall_app Forall_singleton in Hsubsume.
    destruct Hsubsume as [Hsubsume Hc].
    do 2 iNamed "Hgroup".
    (* Obtain proof that [ts] has aborted. *)
    iDestruct (big_sepS_elem_of with "Hsafecp") as "Hc"; first apply Hc.
    simpl.
    iDestruct "Hc" as "[Habt %Hvts]".
    rewrite /group_inv_no_log_with_cpool.
    destruct (stm !! ts) as [st |] eqn:Hdup; last first.
    { (* Case: Directly abort without prepare. *)
      rewrite /group_inv_no_log_no_cpool.
      assert (Hxfinal : cm !! ts = None).
      { by rewrite Hcm lookup_omap Hdup. }
      rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hxfinal.
      (* Insert [(ts, true)] into the commit map. *)
      iMod (group_commit_insert ts false with "Hcm") as "[Hcm _]".
      { apply Hxfinal. }
      (* Re-establish [safe_txnst]. *)
      iDestruct (big_sepM_insert_2 _ _ ts StAborted with "[] Hsafestm") as "Hsafestm'".
      { done. }
      iFrame "∗ # %".
      iPureIntro.
      split; first done.
      split.
      { rewrite dom_insert_L.
        apply (map_Forall_impl _ _ _ Hpmstm).
        intros t b Hb. clear -Hb.
        destruct b; [set_solver | done].
      }
      split.
      { by rewrite Hcm omap_insert /=. }
      split.
      { (* Re-establish [prepared_impl_locked]. *)
        intros t m k Hm Hk.
        destruct (decide (t = ts)) as [-> | Hneq]; first by rewrite lookup_insert_eq in Hm.
        rewrite lookup_insert_ne in Hm; last done.
        by specialize (Hpil _ _ _ Hm Hk).
      }
      split.
      { (* Re-establish [locked_impl_prepared]. *)
        intros k t Ht Hnz.
        destruct (decide (t = ts)) as [-> | Hneq].
        { exfalso.
          specialize (Hlip _ _ Ht Hnz).
          destruct Hlip as (pwrs & Hpwrs & _).
          by rewrite Hpwrs in Hdup.
        }
        rewrite lookup_insert_ne; last done.
        by specialize (Hlip _ _ Ht Hnz).
      }
      { rewrite lookup_insert_ne; first apply Htsnz.
        rewrite /valid_ts in Hvts.
        clear -Hvts. lia.
      }
    }
    (* Case: Txn [ts] has prepared, aborted, or committed. *)
    rewrite /group_inv_no_log_no_cpool.
    (* rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hdup. *)
    destruct st as [pwrs | |] eqn:Hst; first 1 last.
    { (* Case: Committed; contradiction by obtaining a commit token. *)
      iDestruct (big_sepM_lookup with "Hsafestm") as "Hcmt"; first apply Hdup. simpl.
      iDestruct "Hcmt" as (wrs) "Hcmt".
      do 2 iNamed "Htxnsys".
      iDestruct (txn_res_lookup with "Hresm Habt") as %Habt.
      iDestruct (txn_res_lookup with "Hresm Hcmt") as %Hcmt.
      congruence.
    }
    { (* Case: Aborted; no-op. *)
      assert (Habted : cm !! ts = Some false).
      { by rewrite Hcm lookup_omap Hdup. }
      rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Habted.
      by iFrame "∗ # %".
    }
    (* Case: Prepared; release the locks on tuples. *)
    assert (Hxfinal : cm !! ts = None).
    { by rewrite Hcm lookup_omap Hdup. }
    rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm /= Hxfinal.
    set cm' := insert _ _ cm.
    (* Obtain proof of valid prepared input. *)
    iDestruct (big_sepM_lookup with "Hsafestm") as "Hc"; first apply Hdup. simpl.
    iDestruct "Hc" as "[_ Hsafepwrs]".
    iDestruct "Hsafepwrs" as (wrs) "(Hwrs & _ & %Hvwrs & %Hne & %Hpwrs)".
    (* Take the required keys invariants. *)
    iDestruct (big_sepS_subseteq_acc _ _ (dom pwrs) with "Hkeys") as "[Hkeys HkeysC]".
    { (* Prove [dom pwrs ⊆ keys_all] *)
      transitivity (dom wrs); last done.
      rewrite Hpwrs.
      apply dom_filter_subseteq.
    }
    (* Take the required prepare timestamp from the group invariant. *)
    iDestruct (big_sepM_dom_subseteq_difference _ _ (dom pwrs) with "Hlocks")
      as (ptsm [Hdom Hsubseteq]) "[Hptsm HptsmO]".
    { (* Prove [dom pwrs ⊆ dom (tpls_group gid tpls)]. *)
      pose proof (apply_cmds_dom log _ _ Hrsm) as Hdom.
      rewrite Hpwrs wrs_group_keys_group_dom filter_group_keys_group_dom Hdomptsm.
      set_solver.
    }
    (* Expose the prepared timestamp from keys invariant. *)
    iDestruct (keys_inv_extract_tsprep with "Hkeys") as (ptsmk) "(Hkeys & Hptsmk & %Hdomk)".
    (* Agree on the prepare timestamps from the group and keys invariants. *)
    iDestruct (repl_ts_big_agree with "Hptsm Hptsmk") as %->.
    { by rewrite Hdom Hdomk. }
    (* Reset the prepared timestamps. *)
    iMod (repl_ts_big_update (release pwrs ptsm) with "Hptsm Hptsmk") as "[Hptsm Hptsmk]".
    { by rewrite release_dom. }
    (* From [prepared_impl_locked] we know keys in [dom pwrs] must be locked by [ts]. *)
    iAssert ([∗ set] key ∈ dom pwrs, key_inv_no_tsprep γ key ts)%I
      with "[Hkeys]" as "Hkeys".
    { iApply (big_sepM_sepS_impl with "Hkeys"); first done.
      iIntros (k t Ht) "!> Hkey".
      assert (Hk : k ∈ dom pwrs).
      { by rewrite -Hdomk elem_of_dom. }
      specialize (Hpil _ _ _ Hdup Hk).
      assert (Hincl : ptsm ⊆ tspreps).
      { etrans; [apply Hsubseteq | apply map_filter_subseteq]. }
      pose proof (lookup_weaken _ _ _ _ Ht Hincl) as Ht'.
      rewrite Hpil in Ht'.
      inv Ht'.
      (* Looks like [inv Ht'] also gives [h = h'], which is useful, but is that
      the expected behavior? *)
      done.
    }
    (* Prove txn [ts] has prepared but not committed on [tpls]. *)
    iDestruct (keys_inv_prepared (dom pwrs) with "Habt Hkeys Htxnsys") as "[Hkeys Htxnsys]".
    (* Re-establish keys invariant w.r.t. updated prepare timestamps. *)
    iDestruct (keys_inv_learn_abort with "Hkeys") as "Hkeys".
    (* Put ownership of tuples back to keys invariant. *)
    iDestruct (keys_inv_merge_tsprep (dom pwrs) with "[Hkeys] Hptsmk") as "Hkeys".
    { by rewrite release_dom. }
    { iApply (big_sepS_sepM_impl with "Hkeys").
      { by rewrite release_dom. }
      iIntros (k t Ht) "!> Hkey".
      apply elem_of_dom_2 in Ht as Hinptsm.
      rewrite release_dom in Hinptsm.
      pose proof Hinptsm as Hinpwrs. rewrite Hdom in Hinpwrs.
      pose proof (release_modified Hinpwrs Hinptsm) as Hunlocked.
      by inv Hunlocked.
    }
    iDestruct ("HkeysC" with "Hkeys") as "Hkeys".
    (* Merge ownership of prepared timestamp back to group invariant. *)
    iDestruct (repl_ts_release_disjoint pwrs with "HptsmO") as "HptsmO".
    { set_solver. }
    rewrite release_difference_distr.
    iDestruct (big_sepM_subseteq_difference_2 with "Hptsm HptsmO") as "Hptsm".
    { by apply release_mono. }
    rewrite release_filter_group_commute.
    (* Insert [(ts, false)] into the commit map. *)
    iMod (group_commit_insert ts false with "Hcm") as "[Hcm _]".
    { apply Hxfinal. }
    (* Re-establish [valid_prepared]. *)
    iDestruct (big_sepM_insert_2 _ _ ts StAborted with "[] Hsafestm") as "Hsafestm'".
    { iFrame "Habt". }
    iFrame "∗ # %".
    iPureIntro.
    split; first done.
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
