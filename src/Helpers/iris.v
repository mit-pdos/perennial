From iris.proofmode Require Import tactics.
From iris Require Import base_logic.lib.invariants.

Theorem inv_dup_acc {Σ} `{!invG Σ} (Q: iProp Σ) N E (P: iProp Σ) :
  ↑N ⊆ E →
  inv N P -∗
  (P -∗ P ∗ Q) -∗
  |={E}=> ▷ Q.
Proof.
  iIntros (Hsub) "Hinv HPtoQ".
  iInv "Hinv" as "HP" "Hclose".
  iDestruct ("HPtoQ" with "HP") as "[HP HQ]".
  iMod ("Hclose" with "HP") as "_".
  iIntros "!> !>".
  iFrame.
Qed.

Lemma inv_combine_dup {Σ} `{!invG Σ} N (P Q: iProp Σ) :
  □ (P -∗ P ∗ P) -∗
  inv N P -∗ inv N Q -∗ inv N (P ∗ Q).
Proof.
  rewrite inv_eq. iIntros "#HPdup #HinvP #HinvQ !#"; iIntros (E ?).
  iMod ("HinvP" with "[%]") as "[HP HcloseP]"; first set_solver.
  iDestruct ("HPdup" with "HP") as "[$ HP]".
  iMod ("HcloseP" with "HP") as "_".
  iMod ("HinvQ" with "[%]") as "[$ HcloseQ]"; first set_solver.
  iMod (fupd_intro_mask' _ (E ∖ ↑N)) as "Hclose"; first set_solver.
  iIntros "!> [HP HQ]".
  iMod "Hclose" as %_. iMod ("HcloseQ" with "HQ") as %_. auto.
Qed.
