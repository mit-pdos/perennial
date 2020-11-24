From iris.base_logic.lib Require Export mnat.
From Perennial.algebra Require Import own_discrete.

Global Instance mnat_own_auth_discretizable Σ `{mnatG Σ} γ q n
  : Discretizable (mnat_own_auth γ q n).
Proof.
  rewrite mnat_own_auth_eq.
  apply _.
Qed.

Global Instance mnat_own_lb_discretizable Σ `{mnatG Σ} γ n
  : Discretizable (mnat_own_lb γ n).
Proof.
  rewrite mnat_own_lb_eq.
  apply _.
Qed.
