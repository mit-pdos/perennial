From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import iprop.
From iris.bi.lib Require Import fractional.
From Perennial.Helpers Require Import Qextra.

Section bi.
  Context {PROP:bi} `{!BiAffine PROP}.
  Set Default Proof Using "All".

  Implicit Types (P:PROP) (Φ: Qp → PROP) (q: Qp).

  Theorem fractional_weaken Φ `{fractional.Fractional _ Φ} q1 q2 :
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

  Theorem as_fractional_weaken `{!fractional.AsFractional P Φ q2} q1 :
    (q1 ≤ q2)%Qc →
    P -∗ Φ q1.
  Proof.
    iIntros (?) "HP".
    iDestruct (as_fractional (AsFractional:=H) with "HP") as "HΦ".
    iApply fractional_weaken; eauto.
  Qed.

End bi.
