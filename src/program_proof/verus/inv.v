From Perennial.program_proof Require Import grove_prelude.

Section proof.

Context `{!heapGS Σ}.
(* This is to justify the inv_acc rule with lc in Verus *)
Lemma inv_acc N P :
  inv N P -∗
  ∀ E,
  ⌜ ↑N ⊆ E ⌝ -∗ £ 1 -∗
  |={E, E∖↑N}=> (P ∗ (P -∗ |={E∖↑N,E}=> True)).
Proof.
  iIntros "Hinv".
  iIntros (??) "Hlc".
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
  iModIntro.
  iFrame "Hi". iIntros.
  iApply "Hclose". iFrame.
Qed.

End proof.
