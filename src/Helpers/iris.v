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
