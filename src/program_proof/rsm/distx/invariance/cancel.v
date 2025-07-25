From Perennial.program_proof.rsm.distx Require Import prelude.

Section inv.
  Context `{!distx_ghostG Σ}.

  Lemma txnsys_inv_cancel γ tid future :
    head_abort future tid ->
    txns_abt_elem γ tid -∗
    txnwrs_excl γ tid -∗
    txnsys_inv_no_future γ future ==∗
    txnsys_inv_no_future γ (tail future).
  Proof.
    iIntros (Hhead) "Hwabt Hwrsexcl Htxn".
    iNamed "Htxn".
    (* Delete [tid] from [txns_abt_auth]. *)
    iDestruct (txns_abt_elem_of with "Htidas Hwabt") as %Htid.
    iMod (txns_abt_delete with "Hwabt Htidas") as "Htidas".
    (* Insert [(tid, ResAborted)] into [txnres_auth]. *)
    iDestruct (elem_of_tmodas_partitioned_tids _ _ _ _ _ tid with "Hpart") as %Hnotin.
    { by rewrite Htidas. }
    assert (Hresm : resm !! tid = None ∨ resm !! tid = Some ResAborted).
    { destruct (resm !! tid) as [res |] eqn:Hres; last by left.
      right.
      destruct res as [wrs |] eqn:Hwrs.
      { destruct Hnotin as [_ Hnotin]. by specialize (Hnotin wrs). }
      done.
    }
    set resm' := <[tid := ResAborted]> resm.
    iAssert (|==> txnres_auth γ resm')%I with "[Hresm]" as "Hresm".
    { subst resm'.
      destruct Hresm as [Hnone | Hwabt]; last by rewrite insert_id.
      by iApply (txnres_insert with "Hresm").
    }
    iMod "Hresm" as "Hresm".
    (* Re-establish [incorrect_wrs_in_fcc]. *)
    rewrite -Htidas elem_of_dom in Htid.
    destruct Htid as [form Hform].
    iDestruct (big_sepM_delete _ _ tid with "Hiwrs") as "[_ Hiwrs']"; first apply Hform.
    iClear "Hiwrs".
    (* Persist the txn write-set resource. *)
    iMod (txnwrs_excl_persist with "Hwrsexcl") as "Hccl".
    (* Re-establish [valid_res]. *)
    iDestruct (big_sepM_insert_2 _ _ tid ResAborted with "[Hccl] Hvr") as "#Hvr'".
    { iFrame. }
    iClear "Hvr".
    set tmodas' := delete tid tmodas.
    (* Re-establish [partitioned_tids]. *)
    iAssert (partitioned_tids γ tids tmodcs tmodas' resm')%I with "[Hpart]" as "Hpart".
    { iNamed "Hpart".
      rewrite /partitioned_tids dom_delete_L.
      rewrite resm_to_tmods_insert_aborted; last apply Hresm.
      rewrite (big_sepS_delete _ (dom tmodas) tid); last first.
      { by apply elem_of_dom. }
      iDestruct "Hwabts" as "[_ Hwabts]".
      iFrame.
      iPureIntro.
      intros tidx Htidx.
      rewrite dom_insert_L.
      specialize (Hfate _ Htidx).
      clear -Hfate.
      destruct (decide (tidx = tid)) as [-> | Hne]; set_solver.
    }
    iFrame "∗ # %".
    rewrite /cmtxn_in_past resm_to_tmods_insert_aborted; last apply Hresm.
    iFrame.
    iPureIntro.
    split; first set_solver.
    split.
    { subst resm'.
      intros t m Htm.
      specialize (Htidcs _ _ Htm). simpl in Htidcs.
      destruct Htidcs as [? | Hresmt]; first by left.
      right.
      destruct (decide (t = tid)) as [-> | Hne].
      { exfalso. rewrite Hresmt in Hresm. by destruct Hresm. }
      by rewrite lookup_insert_ne.
    }
    split; first set_solver.
    split; first done.
    split.
    { intros tsx wrsx Hwrsx.
      specialize (Hcf _ _ Hwrsx). simpl in Hcf.
      by unshelve eapply (first_commit_compatible_inv_tail_future _ _ _ _ _ Hhead).
    }
    intros tsx formx Hformx.
    destruct (decide (tsx = tid)) as [-> | Hne].
    { by rewrite lookup_delete_eq in Hformx. }
    rewrite lookup_delete_ne in Hformx; last done.
    specialize (Hcp _ _ Hformx). simpl in Hcp.
    rewrite /conflict_cases in Hcp *.
    destruct formx as [| | wrs | wrs].
    - by apply no_commit_abort_inv_tail_future.
    - unshelve eapply (first_abort_inv_tail_future _ _ _ _ Hhead Hcp). inv 1.
    - apply (first_commit_incompatible_inv_tail_future _ _ _ _ _ Hhead Hcp).
    - by unshelve eapply (first_commit_compatible_inv_tail_future _ _ _ _ _ Hhead).
  Qed.

End inv.
