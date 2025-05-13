From Perennial.program_proof.tulip Require Import prelude.

Section inv.
  Context `{!heapGS Σ}.
  Context `{!tulip_ghostG Σ}.

  Lemma txnsys_inv_preprepare γ p Qr tid wrs :
    valid_ts tid ->
    valid_wrs wrs ->
    Qr wrs ->
    is_txn_postcond γ tid Qr -∗
    own_txn_reserved_wrs γ tid -∗
    txnsys_inv γ p ==∗
    txnsys_inv γ p ∗
    is_txn_wrs γ tid wrs.
  Proof.
    iIntros (Hvts Hvwrs HQ) "#HQ Hexclwrs Htxnsys".
    do 2 iNamed "Htxnsys".
    iDestruct (txn_oneshot_wrs_elem_of with "Hexclwrs Hwrsm") as %Hin.
    iMod (txn_oneshot_wrs_update _ _ _ wrs with "Hexclwrs Hwrsm") as "[Hwrsm #Hwrs]".
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
