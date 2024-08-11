From Perennial.program_proof.rsm.distx Require Import prelude.

Lemma cmtd_impl_prep_inv_abort {resm wrsm} ts :
  cmtd_impl_prep resm wrsm ->
  cmtd_impl_prep (<[ts:=ResAborted]> resm) wrsm.
Proof.
  intros Hcip ts'.
  destruct (decide (ts' = ts)) as [-> | Hne]; first by rewrite lookup_insert.
  rewrite lookup_insert_ne; last done.
  by apply Hcip.
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

  Lemma txn_inv_abort γ gid pm ts wrs :
    gid ∈ ptgroups (dom wrs) ->
    txnwrs_receipt γ ts wrs -∗
    txnprep_unprep γ gid ts -∗
    txnprep_auth γ gid pm -∗
    txn_inv γ ==∗
    txnprep_auth γ gid pm ∗
    txn_inv γ ∗
    txnres_abt γ ts.
  Proof.
    iIntros (Hgid) "#Hwrs #Hnp Hpm Htxn".
    iNamed "Htxn".
    destruct (resm !! ts) as [res |] eqn:Hres; last first.
    { (* Case: [ts] not aborted or committed yet. *)
      iMod (txnres_insert ts ResAborted with "Hresm") as "Hresm"; first done.
      iDestruct (txnres_witness with "Hresm") as "#Habt".
      { apply lookup_insert. }
      pose proof (cmtd_impl_prep_inv_abort ts Hcip) as Hcip'.
      iFrame "∗ # %".
      rewrite resm_to_tmods_insert_aborted; last done.
      rewrite big_sepM_insert; last done.
      by iFrame "∗ #".
    }
    destruct res as [wrsc |]; last first.
    { (* Case: [ts] aborted; get a witness without any update. *)
      iDestruct (txnres_witness with "Hresm") as "#Habt".
      { apply Hres. }
      by auto 10 with iFrame.
    }
    (* Case: [ts] committed; contradiction. *)
    iDestruct (big_sepM_lookup with "Hvr") as "#Hresc"; first apply Hres.
    (* Prove [wrsc = wrs]. *)
    iDestruct (txnwrs_lookup with "Hwrsm Hwrs") as %Hwrs.
    specialize (Hcip ts).
    rewrite Hres Hwrs in Hcip.
    inversion Hcip. subst wrsc.
    rewrite /= /all_prepared.
    iDestruct (big_sepS_elem_of with "Hresc") as "Hp"; first apply Hgid.
    iDestruct (txnprep_lookup with "Hpm Hp") as %Hp.
    iDestruct (txnprep_lookup with "Hpm Hnp") as %Hnp.
    congruence.
  Qed.

End inv.
