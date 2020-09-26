From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import iprop.
From iris.bi.lib Require Import fractional.
From Perennial.Helpers Require Import Qextra.

Theorem fractional_weaken {Σ} (Φ : Qp -> iProp Σ) `{fractional.Fractional _ Φ} (q1 q2 : Qp) :
  (q1 ≤ q2)%Qc ->
  Φ q2 -∗ Φ q1.
Proof.
  iIntros (Hle) "H".
  edestruct (Qcanon.Qcle_lt_or_eq); eauto.
  - edestruct Qp_split_lt; eauto.
    rewrite -H1.
    rewrite fractional.
    iDestruct "H" as "[$ _]".
  - apply Qp_eq in H0.
    subst; done.
Qed.
