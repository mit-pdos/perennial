From Perennial.program_proof.tulip Require Import prelude.

Section inv.
  Context `{!tulip_ghostG Σ}.

  Lemma group_inv_submit {γ gid cpool} c :
    safe_submit γ gid c -∗
    group_inv_no_cpool γ gid cpool -∗
    group_inv_no_cpool γ gid ({[c]} ∪ cpool).
  Proof.
    iIntros "Hsafe Hgroup".
    do 2 iNamed "Hgroup".
    iDestruct (big_sepS_insert_2 with "Hsafe Hsafecp") as "Hsafecp'".
    iFrame "∗ # %".
    iPureIntro.
    rewrite /txn_cpool_subsume_log.
    apply (Forall_impl _ _ _ Hcscincl).
    set_solver.
  Qed.

End inv.
