From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fractional.
From Perennial.base_logic.lib Require Import iprop.
From Perennial.Helpers Require Import Qextra.

Section bi.
  Context {PROP:bi} `{!BiAffine PROP}.
  Set Default Proof Using "All".

  Implicit Types (P:PROP) (Φ: Qp → PROP) (q: Qp).

  Theorem fractional_weaken Φ `{fractional.Fractional _ Φ} q1 q2 :
    (q1 ≤ q2)%Qp ->
    Φ q2 -∗ Φ q1.
  Proof.
    iIntros ([Hlt%Qp_split_lt|<-]%Qp_le_lteq) "H".
    - destruct Hlt as [? <-].
      rewrite fractional.
      iDestruct "H" as "[$ _]".
    - done.
  Qed.

  Theorem as_fractional_weaken `{!fractional.AsFractional P Φ q2} q1 :
    (q1 ≤ q2)%Qp →
    P -∗ Φ q1.
  Proof.
    iIntros (?) "HP".
    iDestruct (as_fractional (AsFractional:=H) with "HP") as "HΦ".
    iApply fractional_weaken; eauto.
  Qed.

End bi.
