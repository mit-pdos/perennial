From Perennial.program_proof.rsm.distx Require Import prelude.

Section inv.
  Context `{!distx_ghostG Σ}.

  Lemma txnsys_inv_preprepare γ p Qr tid wrs :
    valid_ts tid ->
    valid_wrs wrs ->
    Qr wrs ->
    txnpost_receipt γ tid Qr -∗
    txnwrs_excl γ tid -∗
    txnsys_inv γ p ==∗
    txnsys_inv γ p ∗
    txnwrs_receipt γ tid wrs.
  Proof.
    iIntros (Hvts Hvwrs HQ) "#HQ Hexclwrs Htxn".
    iNamed "Htxn".
    iDestruct (txnwrs_excl_elem_of with "Hexclwrs Hwrsm") as %Hin.
    iMod (txnwrs_set _ _ _ wrs with "Hexclwrs Hwrsm") as "[Hwrsm #Hwrs]".
    iFrame "∗ # %".
    rewrite wrsm_dbmap_insert_Some.
    iModIntro.
    iSplit.
    { iApply big_sepM_insert_2; [iFrame "# %" | done]. }
    iPureIntro.
    split; first set_solver.
    by apply map_Forall_insert_2.
  Qed.

End inv.
