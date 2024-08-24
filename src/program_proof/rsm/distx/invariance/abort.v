From Perennial.program_proof.rsm.distx Require Import prelude.

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

  Lemma txnsys_inv_abort γ ts :
    some_aborted γ ts -∗
    txnsys_inv γ ==∗
    txnsys_inv γ ∗
    txnres_abt γ ts.
  Proof.
    iIntros "#Habt Htxn".
    iNamed "Htxn".
    destruct (resm !! ts) as [res |] eqn:Hres; last first.
    { (* Case: [ts] has neither aborted nor committed yet. *)
      iMod (txnres_insert ts ResAborted with "Hresm") as "Hresm"; first done.
      iDestruct (txnres_witness with "Hresm") as "#Hreceipt".
      { apply lookup_insert. }
      iFrame "∗ # %".
      rewrite /partitioned_tids resm_to_tmods_insert_aborted; last done.
      rewrite big_sepM_insert; last done.
      iFrame "∗ #".
      iPureIntro.
      by rewrite /cmtxn_in_past resm_to_tmods_insert_aborted; last apply Hres.
    }
    destruct res as [wrsc |]; last first.
    { (* Case: [ts] aborted; get a witness without any update. *)
      iDestruct (txnres_witness with "Hresm") as "#Hreceipt"; first apply Hres.
      by iFrame "∗ # %".
    }
    (* Case: [ts] committed; contradiction. *)
    iDestruct (big_sepM_lookup with "Hvr") as "#Hprep"; first apply Hres.
    simpl.
    iDestruct (all_prepared_some_aborted_false with "Hprep Habt") as %[].
  Qed.

End inv.
