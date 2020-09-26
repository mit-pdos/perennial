From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import iprop.
From iris.bi.lib Require Import fractional.
From Perennial.Helpers Require Import Qextra.

Theorem fractional_weaken q {Σ} (Φ : Qp -> iProp Σ) `{fractional.Fractional _ Φ} :
  Φ 1%Qp -∗ Φ q.
Proof.
  iIntros "H".
  destruct (decide (q = 1%Qp)); subst; try done.
  destruct (decide (Qcanon.Qclt q 1)); subst.
  {
    destruct (Qextra.Qp_split_1 q) as [q' Hqq']; eauto.
    rewrite -Hqq'.
    rewrite fractional.
    iDestruct "H" as "[$ _]".
  }
  (* XXX ??? *)
  admit.
Admitted.
