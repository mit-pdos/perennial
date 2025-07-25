From Perennial.program_proof.rsm.distx Require Import prelude.

Section inv.
  Context `{!distx_ghostG Σ}.

  Lemma txnsys_inv_abort γ tid future :
    head_abort future tid ->
    txnres_abt γ tid -∗
    txns_abt_elem γ tid -∗
    txnsys_inv_no_future γ future ==∗
    txnsys_inv_no_future γ (tail future).
  Proof.
    iIntros (Hhead) "#Habt Hwabt Htxn".
    iNamed "Htxn".
    (* Obtain [tid ∈ dom resm]. *)
    iDestruct (txnres_lookup with "Hresm Habt") as %Habt.
    (* Delete [tid] from [txns_abt_auth]. *)
    iDestruct (txns_abt_elem_of with "Htidas Hwabt") as %Htid.
    iMod (txns_abt_delete with "Hwabt Htidas") as "Htidas".
    (* Re-establish [incorrect_wrs_in_fcc]. *)
    rewrite -Htidas elem_of_dom in Htid.
    destruct Htid as [form Hform].
    iDestruct (big_sepM_delete _ _ tid with "Hiwrs") as "[_ Hiwrs']"; first apply Hform.
    iClear "Hiwrs".
    (* Re-establish [partitioned_tids]. *)
    set tmodas' := delete tid tmodas.
    iAssert (partitioned_tids γ tids tmodcs tmodas' resm)%I with "[Hpart]" as "Hpart".
    { iNamed "Hpart".
      rewrite /partitioned_tids dom_delete_L.
      rewrite (big_sepS_delete _ (dom tmodas) tid); last first.
      { by apply elem_of_dom. }
      iDestruct "Hwabts" as "[_ Hwabts]".
      iFrame.
      iPureIntro.
      intros tidx Htidx.
      specialize (Hfate _ Htidx). simpl in Hfate.
      clear -Hfate Habt.
      apply elem_of_dom_2 in Habt.
      destruct (decide (tidx = tid)) as [-> | Hne]; set_solver.
    }
    iFrame "∗ # %".
    iPureIntro.
    split; first set_solver.
    split; first set_solver.
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
