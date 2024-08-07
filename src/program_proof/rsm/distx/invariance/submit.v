From Perennial.program_proof.rsm.distx Require Import prelude.

Section inv.
  Context `{!distx_ghostG Σ}.

  Lemma group_inv_submit γ gid cpool c :
    safe_submit γ gid c -∗
    group_inv_no_cpool γ gid cpool -∗
    group_inv_no_cpool γ gid ({[c]} ∪ cpool).
  Proof.
    iIntros "Hsafe Hgroup".
    do 2 iNamed "Hgroup".
    iDestruct (big_sepS_insert_2 with "Hsafe Hvc") as "Hvc'".
    iFrame "∗ # %".
  Qed.

End inv.
