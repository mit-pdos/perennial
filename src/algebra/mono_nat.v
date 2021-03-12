From Perennial.base_logic.lib Require Export mono_nat.
From Perennial.algebra Require Import own_discrete.

Global Instance mono_nat_own_auth_discretizable Σ `{mono_natG Σ} γ q n
  : Discretizable (mono_nat_auth_own γ q n).
Proof.
  rewrite mono_nat_auth_own_eq.
  apply _.
Qed.

Global Instance mono_nat_lb_own_discretizable Σ `{mono_natG Σ} γ n
  : Discretizable (mono_nat_lb_own γ n).
Proof.
  rewrite mono_nat_lb_own_eq.
  apply _.
Qed.
