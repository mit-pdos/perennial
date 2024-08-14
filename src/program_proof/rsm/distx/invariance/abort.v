From Perennial.program_proof.rsm.distx Require Import prelude.

Lemma lnrz_txns_destined_inv_abort {tids tmodcs tmodas resm} ts :
  resm !! ts = None ->
  lnrz_txns_destined tids tmodcs tmodas resm ->
  lnrz_txns_destined tids tmodcs tmodas (<[ts := ResAborted]> resm).
Proof.
  intros Hnone.
  by rewrite /lnrz_txns_destined resm_to_tmods_insert_aborted.
Qed.

Lemma resm_to_tmods_insert_aborted resm ts :
  resm !! ts = None ->
  resm_to_tmods (<[ts := ResAborted]> resm) = resm_to_tmods resm.
Proof.
  intros Hnotin.
  rewrite /resm_to_tmods omap_insert_None; last done.
  rewrite delete_notin; first done.
  by rewrite lookup_omap Hnotin.
Qed.

Section inv.
  Context `{!distx_ghostG Σ}.

  Lemma txn_inv_abort γ ts :
    some_aborted γ ts -∗
    txn_inv γ ==∗
    txn_inv γ ∗
    txnres_abt γ ts.
  Proof.
    iIntros "#Habt Htxn".
    iNamed "Htxn".
    destruct (resm !! ts) as [res |] eqn:Hres; last first.
    { (* Case: [ts] has neither aborted nor committed yet. *)
      iMod (txnres_insert ts ResAborted with "Hresm") as "Hresm"; first done.
      iDestruct (txnres_witness with "Hresm") as "#Hreceipt".
      { apply lookup_insert. }
      pose proof (lnrz_txns_destined_inv_abort ts Hres Hdest) as Hdest'.
      iFrame "∗ # %".
      rewrite resm_to_tmods_insert_aborted; last done.
      rewrite big_sepM_insert; last done.
      by iFrame "∗ #".
    }
    destruct res as [wrsc |]; last first.
    { (* Case: [ts] aborted; get a witness without any update. *)
      iDestruct (txnres_witness with "Hresm") as "#Hreceipt"; first apply Hres.
      by auto 10 with iFrame.
    }
    (* Case: [ts] committed; contradiction. *)
    iDestruct (big_sepM_lookup with "Hvr") as "#Hprep"; first apply Hres.
    simpl.
    iDestruct (all_prepared_some_aborted_false with "Hprep Habt") as %[].
  Qed.

End inv.
